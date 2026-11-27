module

public import Lens.Basic
public import Lens.Relation
public import Lens.Frame
public import Lens.ProdFrame
public import Lens.Derive
public import Lens.Tactics.Disjoint
public import Lens.ExtraNotation
public meta import Lean

/-!
# Demand-Driven Forward-Extraction & Frame-Rewriting Tactics (`lens_eqs`, `lens_rw`)

Architecture-independent, demand-driven preservation extraction and rewriting built purely on
`Optic` (`Lens`, `Getter`, `Iso`, `Modifies`, `ReflTransGen`, `EqOn`, `EqOnAll`, `ModifiesAny`)
and `Optic.Tactic` (`proveDisjoint?`, `proveIndependent?`).

Provides in `namespace Optic.Tactic`:
- `FrameHyp` / `FrameHypKind`, `parseFrameHyp?`, `collectFrameHyps`: recognizes frame hypotheses
  of the form `ReflTransGen (Modifies l) s' s`, `Modifies l s' s`, `EqOn g s' s`, `EqOnAll gs s' s`,
  `ModifiesAny ls s' s`, and `s' = {ₗ s₀ with … }`.
- `provePreservedEq?`: proves `g.get s' = <normalized rhs>` for a frame hypothesis and getter,
  normalizing `{ₗ s₀ with l₁ := v₁, l₂ over f₂, … }` update chains on the RHS into clean field
  values (`st.pc = 16`, `st.data.regs.x0 = s₀.data.regs.x0 + 1`, `st.data.dmem = s₀.data.dmem`).
- `findConflictingWriteLens?`: splits a product write lens via `splitProdTree` to pinpoint the
  specific conflicting write factor for diagnostics.
- `frameEqsFor` / `frameEqsInContext`: demand-driven subterm scanner with outermost-preserved-prefix
  collapsing (whole-map `dmem` collapsing and redundant sub-projection subsumption), deduplication
  up to reducible defeq, and readable hypothesis naming.
- `mkFrameRwSimprocs` / `mkFrameRwMethods`: custom `Simp.Simproc` / `Simp.Methods` pass that
  rewrites preserved subterms on the fly across multi-hop frame chains (`s₂ → s₁ → s₀`) with
  cycle avoidance and zero context pollution.
- `lens_eqs`, `lens_eqs h`, `lens_eqs h [p₁, p₂, …]`, and `lens_rw (at …)?` tactics.
-/

public meta section

open Lean Meta Elab Tactic

namespace Optic.Tactic

/-! ### Expression & List Utilities -/

/-- Check whether `needle` occurs syntactically inside `hay`, using the fast FVar cache when
`needle` is a free variable. -/
private def exprOccurs (needle hay : Expr) : Bool :=
  if needle.isFVar then
    hay.containsFVar needle.fvarId!
  else
    (hay.find? (· == needle)).isSome

/-- Replace all occurrences of `target` in `e` with `repl`. -/
private def replaceExprExact (e target repl : Expr) : Expr :=
  if target.isFVar then
    e.replaceFVar target repl
  else
    e.replace fun sub => if sub == target then some repl else none

/-- Extract the elements of a literal `List` expression (`[]`, `a :: b :: …`), returning `none` if
the tail is symbolic. -/
private partial def literalListElems? (e : Expr) : MetaM (Option (Array Expr)) := do
  let e ← whnfD (← instantiateMVars e)
  if e.isAppOfArity ``List.nil 1 then
    return some #[]
  if e.isAppOfArity ``List.cons 3 then
    let head := e.getArg! 1
    let tail := e.getArg! 2
    let some rest ← literalListElems? tail | return none
    return some (#[head] ++ rest)
  return none

/-- Build a proof of `elem ∈ listExpr` where `elem` sits at index `idx` of a literal list. -/
private partial def mkListMemProof (elemTy elem listExpr : Expr) (idx : Nat) : MetaM Expr := do
  let listExpr ← whnfD (← instantiateMVars listExpr)
  if idx == 0 then
    mkAppOptM ``List.mem_cons_self #[some elemTy, some elem, some (listExpr.getArg! 2)]
  else
    let rest ← mkListMemProof elemTy elem (listExpr.getArg! 2) (idx - 1)
    mkAppM ``List.mem_cons_of_mem #[listExpr.getArg! 1, rest]

/-- Check whether two flattened `Lens.comp` chains have equal length and elementwise reducible
definitional equality. -/
private def compChainsDefEq (c₁ c₂ : Array Expr) : MetaM Bool := do
  if c₁.size != c₂.size then return false
  for i in [0:c₁.size] do
    unless ← withReducible (isDefEq c₁[i]! c₂[i]!) do
      return false
  return true

/-- Check whether `prefixChain` is a strict prefix of `fullChain` (elementwise reducible defeq). -/
private def compChainIsStrictPrefix (prefixChain fullChain : Array Expr) : MetaM Bool := do
  if prefixChain.size >= fullChain.size then return false
  for i in [0:prefixChain.size] do
    unless ← withReducible (isDefEq prefixChain[i]! fullChain[i]!) do
      return false
  return true

/-- Check whether a type `ty` lives in `Type v` (i.e. not `Prop`), so `Getter s ty` is well-typed. -/
private def isTypeValued (ty : Expr) : MetaM Bool := do
  try
    let sort ← whnf (← inferType ty)
    return sort.isSort && !sort.sortLevel!.isAlwaysZero
  catch _ =>
    return false

/-! ### Lens-Update Chain Recognition (`{ₗ s₀ with … }` / `& l .~ v` / `& l %~ f`) -/

/-- A single outermost lens update step on a state expression. -/
private inductive LensUpdateStep where
  | set (lens base val : Expr)
  | over (lens fn base : Expr)

/-- Recognize an outermost `Lens.set`, `Lens.over`, `setOf`, `overOf`, or `pipe` update step. -/
private partial def peelLensUpdate? (e : Expr) : MetaM (Option LensUpdateStep) := do
  let e := (← instantiateMVars e).consumeMData
  if e.isAppOfArity ``Optic.Lens.set 5 then
    return some (.set (e.getArg! 2) (e.getArg! 3) (e.getArg! 4))
  if e.isAppOfArity ``Optic.Lens.over 5 then
    return some (.over (e.getArg! 2) (e.getArg! 3) (e.getArg! 4))
  if e.isAppOfArity ``Optic.Notation.setOf 5 then
    return some (.set (e.getArg! 2) (e.getArg! 4) (e.getArg! 3))
  if e.isAppOfArity ``Optic.Notation.overOf 5 then
    return some (.over (e.getArg! 2) (e.getArg! 3) (e.getArg! 4))
  if e.isAppOfArity ``Optic.Notation.pipe 4 then
    let base := e.getArg! 2
    let fn := e.getArg! 3
    let reduced := (mkApp fn base).headBeta
    if reduced != e then
      return ← peelLensUpdate? reduced
  return none

/-- Return the underlying base state at the bottom of a (possibly empty) lens-update chain. -/
private partial def baseStateOfUpdates (e : Expr) : MetaM Expr := do
  match ← peelLensUpdate? e with
  | some (.set _ base _) => baseStateOfUpdates base
  | some (.over _ _ base) => baseStateOfUpdates base
  | none => return (← instantiateMVars e).consumeMData

/-! ### 1. Frame Hypothesis Recognizer (`FrameHyp`, `parseFrameHyp?`, `collectFrameHyps`) -/

/-- Classification of a recognized frame hypothesis relating `lhs` (`s'`) and `rhs` (`s`). -/
inductive FrameHypKind where
  | rtModifies (writeLens : Expr)
  | modifies (writeLens : Expr)
  | eqOn (getter : Expr)
  | eqOnAll (listExpr : Expr)
  | modifiesAny (listExpr : Expr)
  | eqUpdate
  deriving Inhabited

/-- A parsed local frame hypothesis `proof : <FrameRel> lhs rhs` over state type `stateType`. -/
structure FrameHyp where
  proof : Expr
  kind : FrameHypKind
  stateType : Expr
  lhs : Expr
  rhs : Expr
  deriving Inhabited

/-- Recognize `Optic.Modifies l` (possibly eta-expanded as `fun x y => Optic.Modifies l x y`). -/
private def extractModifiesRelLens? (rel : Expr) : Option Expr :=
  let rel := rel.consumeMData
  if rel.isAppOfArity ``Optic.Modifies 3 then
    some (rel.getArg! 2)
  else
    match rel with
    | .lam _ _ (.lam _ _ body _) _ =>
      let body := body.consumeMData
      if body.isAppOfArity ``Optic.Modifies 5 &&
          body.getArg! 3 == .bvar 1 && body.getArg! 4 == .bvar 0 then
        some (body.getArg! 2)
      else
        none
    | _ => none

/-- Attempt to parse a hypothesis term `h` as a `FrameHyp`. Supports:
- `ReflTransGen (Modifies l) s' s` (`≡ₚ … except […]`, `st is { s₀ with … except … }`),
- `Modifies l s' s`,
- `EqOn g s' s`,
- `EqOnAll gs s' s` (`≡ₚ … on […]` / `≡ₗ … on […]`),
- `ModifiesAny ls s' s` (`≡ₗ … except […]`),
- `s' = {ₗ s₀ with … }` (`st is { s₀ with … }` without `except`). -/
def parseFrameHyp? (h : Expr) : MetaM (Option FrameHyp) := do
  let ty := (← instantiateMVars (← inferType h)).consumeMData
  -- 1. `ReflTransGen (Modifies l) s' s`
  if ty.isAppOfArity ``Optic.ReflTransGen 4 then
    let stateType := ty.getArg! 0
    let rel := ty.getArg! 1
    let lhs := (ty.getArg! 2).consumeMData
    let rhs := (ty.getArg! 3).consumeMData
    if let some writeLens := extractModifiesRelLens? rel then
      return some { proof := h, kind := .rtModifies writeLens, stateType, lhs, rhs }
  -- 2. `Modifies l s' s`
  if ty.isAppOfArity ``Optic.Modifies 5 then
    return some {
      proof := h
      kind := .modifies (ty.getArg! 2)
      stateType := ty.getArg! 0
      lhs := (ty.getArg! 3).consumeMData
      rhs := (ty.getArg! 4).consumeMData
    }
  -- 3. `EqOn g s' s`
  if ty.isAppOfArity ``Optic.EqOn 5 then
    return some {
      proof := h
      kind := .eqOn (ty.getArg! 2)
      stateType := ty.getArg! 0
      lhs := (ty.getArg! 3).consumeMData
      rhs := (ty.getArg! 4).consumeMData
    }
  -- 4. `EqOnAll gs s' s`
  if ty.isAppOfArity ``Optic.EqOnAll 4 then
    return some {
      proof := h
      kind := .eqOnAll (ty.getArg! 1)
      stateType := ty.getArg! 0
      lhs := (ty.getArg! 2).consumeMData
      rhs := (ty.getArg! 3).consumeMData
    }
  -- 5. `ModifiesAny ls s' s`
  if ty.isAppOfArity ``Optic.ModifiesAny 4 then
    return some {
      proof := h
      kind := .modifiesAny (ty.getArg! 1)
      stateType := ty.getArg! 0
      lhs := (ty.getArg! 2).consumeMData
      rhs := (ty.getArg! 3).consumeMData
    }
  -- 6. `s' = {ₗ s₀ with … }` (from `st is { s₀ with … }` without `except`)
  if let some (stateType, lhs, rhs) := ty.eq? then
    let rhs := rhs.consumeMData
    if (← peelLensUpdate? rhs).isSome then
      return some {
        proof := h
        kind := .eqUpdate
        stateType
        lhs := lhs.consumeMData
        rhs
      }
  return none

/-- Collect all recognized `FrameHyp`s from the current local context (excluding implementation
details). -/
def collectFrameHyps : MetaM (Array FrameHyp) := do
  let mut acc := #[]
  for decl in (← getLCtx) do
    if decl.isImplementationDetail then continue
    if let some fh ← parseFrameHyp? decl.toExpr then
      acc := acc.push fh
  return acc

/-! ### Pretty Rendering of Getter/Lens Applications -/

/-- Apply a single atomic projectable lens segment (`make_lenses` field, `fst`, `snd`, `atKey`) to
`base`, returning `none` for opaque/custom lenses (like bit-slices or abstract lens variables). -/
private def applyProjectableSegment? (seg base : Expr) : MetaM (Option Expr) := do
  let seg ← whnfOptic seg
  let env ← getEnv
  if seg.isAppOfArity ``Optic.Lens.id 1 then
    return some base
  if seg.isAppOfArity ``Optic.Lens.fst 2 then
    return some (← mkAppM ``Prod.fst #[base])
  if seg.isAppOfArity ``Optic.Lens.snd 2 then
    return some (← mkAppM ``Prod.snd #[base])
  if seg.isAppOfArity ``Optic.Lens.atKey 4 then
    let key := seg.getArg! 3
    return some (mkApp base key)
  if let some c := seg.getAppFn.constName? then
    if let some info := Optic.Derive.lookupLensField? env c then
      if let some pfn := getProjFnForField? env info.structName info.fieldName then
        try
          return some (← mkAppM pfn #[base])
        catch _ =>
          return some (mkProj info.structName info.fieldIdx base)
      return some (mkProj info.structName info.fieldIdx base)
  return none

/-- Pretty-render `l.get state` as a natural projection chain (`st.data.regs.x0`, `st.data.dmem k`)
whenever every segment of `l` is a `make_lenses` field, `fst`, `snd`, or `atKey`; otherwise keep
`l.get state` intact so custom lenses like `stX0Low8` are not unfolded. -/
private def renderLensApp (l state : Expr) : MetaM Expr := do
  let segs ← splitCompChain l
  if segs.isEmpty then
    return state
  let mut cur := state
  let mut allProjectable := true
  for seg in segs do
    match ← applyProjectableSegment? seg cur with
    | some next => cur := next
    | none =>
      allProjectable := false
      break
  if allProjectable then
    return cur
  mkAppM ``Optic.Lens.get #[l, state]

/-- Pretty-render `getter.get state` in a form definitionally equal to `Optic.Getter.get getter state`. -/
private partial def renderGetterApp (getter state : Expr) : MetaM Expr := do
  let ng ← whnfOptic getter
  if ng.isAppOfArity ``Optic.Getter.of 3 then
    return (mkApp (ng.getArg! 2) state).headBeta
  if ng.isAppOfArity ``Optic.Getter.id 1 then
    return state
  if ng.isAppOfArity ``Optic.Getter.const 3 then
    return ng.getArg! 2
  if ng.isAppOfArity ``Optic.Getter.map 5 then
    let inner ← renderGetterApp (ng.getArg! 4) state
    return (mkApp (ng.getArg! 3) inner).headBeta
  if ng.isAppOfArity ``Optic.Getter.comp 5 then
    let mid ← renderGetterApp (ng.getArg! 3) state
    return ← renderGetterApp (ng.getArg! 4) mid
  if ng.isAppOfArity ``Optic.Getter.prod 5 then
    let a ← renderGetterApp (ng.getArg! 3) state
    let b ← renderGetterApp (ng.getArg! 4) state
    return ← mkAppM ``Prod.mk #[a, b]
  if ng.isAppOfArity ``Optic.Iso.toGetter 3 then
    return ← mkAppM ``Optic.Iso.to #[ng.getArg! 2, state]
  if ng.isAppOfArity ``Optic.Lens.toGetter 3 then
    return ← renderLensApp (ng.getArg! 2) state
  mkAppM ``Optic.Getter.get #[getter, state]

/-- Extract the underlying `Getter S α` from an `AnyGetter S` expression. -/
private def extractAnyGetter (ag : Expr) : MetaM Expr := do
  let agW ← whnf (← instantiateMVars ag)
  if agW.isAppOfArity ``Optic.AnyGetter.of 3 then
    return (agW.getArg! 2).consumeMData
  mkAppM ``Optic.AnyGetter.getter #[ag]

/-- Extract the underlying `Lens S α` from an `AnyLens S` expression. -/
private def extractAnyLens (al : Expr) : MetaM Expr := do
  let alW ← whnf (← instantiateMVars al)
  if alW.isAppOfArity ``Optic.AnyLens.of 3 then
    return (alW.getArg! 2).consumeMData
  mkAppM ``Optic.AnyLens.lens #[al]

/-! ### 2. Targeted Preservation Prover & RHS Update-Chain Normalization -/

/-- Result of normalizing `getter.get state` across a chain of `Lens.set` / `Lens.over` updates. -/
private structure NormResult where
  rhs : Expr
  proof : Expr -- proves `getter.get state = rhs` (up to defeq)
  clean : Bool -- `true` iff no update step in `state` blocked normalization

/-- Normalize `getter.get state` when `state` is a lens-update chain `{ₗ s₀ with … }`, returning
`(rhs, prf, clean)` where `prf : getter.get state = rhs`. -/
private partial def normalizeGetterOnUpdates (getter state : Expr) (fuel : Nat := 32) :
    MetaM NormResult := do
  if fuel == 0 then
    let r ← renderGetterApp getter state
    return { rhs := r, proof := ← mkEqRefl r, clean := false }
  let some step ← peelLensUpdate? state
    | do
      let r ← renderGetterApp getter state
      return { rhs := r, proof := ← mkEqRefl r, clean := true }

  let (u, base) := match step with
    | .set l b _ => (l, b)
    | .over l _ b => (l, b)

  -- Case A: update lens `u` is independent of `getter` — peel the step directly!
  if let some hind ← proveIndependent? u getter then
    let hStep ← match step with
      | .set _ b val => pure (mkApp2 hind b val)
      | .over l fn b =>
        let newVal := mkApp fn (← mkAppM ``Optic.Lens.get #[l, b])
        pure (mkApp2 hind b newVal)
    let rest ← normalizeGetterOnUpdates getter base (fuel - 1)
    let hTotal ← mkEqTrans hStep rest.proof
    return { rhs := rest.rhs, proof := hTotal, clean := rest.clean }

  -- Case B: `getter` is `Lens.toGetter k` matching or extending `u`
  let ng ← whnfOptic getter
  if ng.isAppOfArity ``Optic.Lens.toGetter 3 then
    let k := ng.getArg! 2
    let uChain ← splitCompChain u
    let kChain ← splitCompChain k
    -- Subcase B1: exact lens match (`u ≡ k` up to `∘ₗ` re-association)
    if ← compChainsDefEq uChain kChain then
      if (← synthLawfulLens? u).isSome then
        match step with
        | .set _ b val =>
          let hStep ← mkAppM ``Optic.Lens.get_set #[u, b, val]
          return { rhs := val, proof := hStep, clean := true }
        | .over _ fn b =>
          let hStep ← mkAppM ``Optic.Lens.get_over #[u, fn, b]
          let inner ← normalizeGetterOnUpdates getter b (fuel - 1)
          let hCongr ← mkCongrArg fn inner.proof
          let hTotal ← mkEqTrans hStep hCongr
          let rhs := (mkApp fn inner.rhs).headBeta
          return { rhs, proof := hTotal, clean := inner.clean }
    -- Subcase B2: `u` is a strict prefix of `k` (`k = u ∘ₗ tail`)
    if ← compChainIsStrictPrefix uChain kChain then
      if (← synthLawfulLens? u).isSome then
        let tail ← mkCompChain (kChain.extract uChain.size kChain.size)
        let tailGetter ← mkAppM ``Optic.Lens.toGetter #[tail]
        let tailGetFn ← mkAppM ``Optic.Lens.get #[tail]
        match step with
        | .set _ b val =>
          let hOuter ← mkAppM ``Optic.Lens.get_set #[u, b, val]
          let hCongr ← mkCongrArg tailGetFn hOuter
          let inner ← normalizeGetterOnUpdates tailGetter val (fuel - 1)
          let hTotal ← mkEqTrans hCongr inner.proof
          return { rhs := inner.rhs, proof := hTotal, clean := inner.clean }
        | .over _ fn b =>
          let uGetter ← mkAppM ``Optic.Lens.toGetter #[u]
          let hOuter ← mkAppM ``Optic.Lens.get_over #[u, fn, b]
          let innerU ← normalizeGetterOnUpdates uGetter b (fuel - 1)
          let hOuter' ← mkEqTrans hOuter (← mkCongrArg fn innerU.proof)
          let hCongr ← mkCongrArg tailGetFn hOuter'
          let valExpr := (mkApp fn innerU.rhs).headBeta
          let inner ← normalizeGetterOnUpdates tailGetter valExpr (fuel - 1)
          let hTotal ← mkEqTrans hCongr inner.proof
          return { rhs := inner.rhs, proof := hTotal, clean := innerU.clean && inner.clean }

  -- Case C: `u` is a product lens `u₁ ×ₗ u₂` inside `.set`: expand into sequential sets
  if let .set _ b val := step then
    let uWhnf ← whnfOptic u
    if uWhnf.isAppOfArity ``Optic.Lens.prod 5 then
      let u₁ := uWhnf.getArg! 3
      let u₂ := uWhnf.getArg! 4
      let (v₁, v₂) ←
        if val.isAppOfArity ``Prod.mk 4 then
          pure (val.getArg! 2, val.getArg! 3)
        else
          pure (← mkAppM ``Prod.fst #[val], ← mkAppM ``Prod.snd #[val])
      let innerState ← mkAppM ``Optic.Lens.set #[u₁, b, v₁]
      let expandedState ← mkAppM ``Optic.Lens.set #[u₂, innerState, v₂]
      return ← normalizeGetterOnUpdates getter expandedState (fuel - 1)

  -- Case D: structural getter combinators (`map`, `comp`, `prod`)
  if ng.isAppOfArity ``Optic.Getter.map 5 then
    let fn := ng.getArg! 3
    let g₁ := ng.getArg! 4
    let r₁ ← normalizeGetterOnUpdates g₁ state (fuel - 1)
    if r₁.clean then
      let hCongr ← mkCongrArg fn r₁.proof
      return { rhs := (mkApp fn r₁.rhs).headBeta, proof := hCongr, clean := true }

  if ng.isAppOfArity ``Optic.Getter.prod 5 then
    let g₁ := ng.getArg! 3
    let g₂ := ng.getArg! 4
    let r₁ ← normalizeGetterOnUpdates g₁ state (fuel - 1)
    let r₂ ← normalizeGetterOnUpdates g₂ state (fuel - 1)
    if r₁.clean && r₂.clean then
      let prodEq ← mkAppM ``Prod.ext #[r₁.proof, r₂.proof]
      let rhs ← mkAppM ``Prod.mk #[r₁.rhs, r₂.rhs]
      return { rhs, proof := prodEq, clean := true }

  -- Stuck: an update step touches `getter` in a way we cannot simplify cleanly
  let r ← renderGetterApp getter state
  return { rhs := r, proof := ← mkEqRefl r, clean := false }

/-- Attempt to derive `getter.get s' = getter.get s` from a single preservation proof
`hBase : g₀.get s' = g₀.get s` (exact match, lens prefix extension, or getter map/comp). -/
private partial def deriveFromGetterEq? (g₀ hBase getter : Expr) : MetaM (Option Expr) := do
  -- 1. Direct definitional match (guarding value type compatibility first)
  let g₀Ty ← whnf (← inferType g₀)
  let gTy ← whnf (← inferType getter)
  if g₀Ty.isAppOfArity ``Optic.Getter 2 && gTy.isAppOfArity ``Optic.Getter 2 then
    if ← isDefEq (g₀Ty.getArg! 1) (gTy.getArg! 1) then
      if ← (withReducible (isDefEq g₀ getter) <||> isDefEq g₀ getter) then
        return some hBase

  let ng₀ ← whnfOptic g₀
  let ng ← whnfOptic getter

  -- 2. Prefix extension: `g₀ = l₀.toGetter`, `getter = (l₀ ∘ₗ tail).toGetter`
  if ng₀.isAppOfArity ``Optic.Lens.toGetter 3 && ng.isAppOfArity ``Optic.Lens.toGetter 3 then
    let c₀ ← splitCompChain (ng₀.getArg! 2)
    let c ← splitCompChain (ng.getArg! 2)
    if ← compChainIsStrictPrefix c₀ c then
      let tail ← mkCompChain (c.extract c₀.size c.size)
      let tailGet ← mkAppM ``Optic.Lens.get #[tail]
      return some (← mkCongrArg tailGet hBase)

  -- 3. `Getter.map f g₁` or `Getter.comp g₁ g₂`
  if ng.isAppOfArity ``Optic.Getter.map 5 then
    if let some h₁ ← deriveFromGetterEq? g₀ hBase (ng.getArg! 4) then
      return some (← mkCongrArg (ng.getArg! 3) h₁)
  if ng.isAppOfArity ``Optic.Getter.comp 5 then
    if let some h₁ ← deriveFromGetterEq? g₀ hBase (ng.getArg! 3) then
      let g₂Get ← mkAppM ``Optic.Getter.get #[ng.getArg! 4]
      return some (← mkCongrArg g₂Get h₁)
  return none

/-- Close a goal of the form `Independent l.lens getter` given `hmem : l ∈ curList` by casing
on list membership. -/
private partial def closeAnyLensMem (proofs : Array Expr) (g : MVarId) (hmem : FVarId)
    (curList : Expr) (idx : Nat) : MetaM Bool := do
  let curListW ← whnfD curList
  if curListW.isAppOfArity ``List.nil 1 then
    let sgs ← g.cases hmem
    return sgs.isEmpty
  if curListW.isAppOfArity ``List.cons 3 then
    let sgs ← g.cases hmem
    let #[sgHead, sgTail] := sgs | return false
    sgHead.mvarId.withContext do
      let tgt ← sgHead.mvarId.getType
      sgHead.mvarId.assign (← mkExpectedTypeHint proofs[idx]! tgt)
    let hTail? ← sgTail.mvarId.withContext do
      for f in sgTail.fields do
        if f.isFVar then
          let fTy ← inferType f
          if fTy.isAppOf ``List.Mem || fTy.isAppOf ``Membership.mem then
            return some f.fvarId!
      return none
    let some hTail := hTail? | return false
    return ← closeAnyLensMem proofs sgTail.mvarId hTail (curListW.getArg! 2) (idx + 1)
  return false

/-- Prove `∀ l ∈ listExpr, Independent l.lens getter` for a literal `List (AnyLens S)`. -/
private def proveAllAnyLensIndep? (listExpr getter : Expr) : MetaM (Option Expr) := do
  let some elems ← literalListElems? listExpr | return none
  let mut proofs : Array Expr := #[]
  for al in elems do
    let l ← extractAnyLens al
    let some hind ← proveIndependent? l getter | return none
    proofs := proofs.push hind
  let listTy ← whnf (← inferType listExpr)
  unless listTy.isAppOfArity ``List 1 do return none
  let anyLensTy := listTy.getArg! 0
  let goalTy ← withLocalDeclD `l anyLensTy fun lVar => do
    let memTy ← mkAppM ``Membership.mem #[listExpr, lVar]
    let lLens ← mkAppM ``Optic.AnyLens.lens #[lVar]
    let indepTy ← mkAppM ``Optic.Independent #[lLens, getter]
    let imp ← mkArrow memTy indepTy
    mkForallFVars #[lVar] imp
  let mvar ← mkFreshExprMVar goalTy
  let ok ← commitWhen do
    try
      let (xs, g') ← mvar.mvarId!.introN 2
      if xs.size != 2 then return false
      closeAnyLensMem proofs g' xs[1]! listExpr 0
    catch _ =>
      return false
  if ok then
    return some (← instantiateMVars mvar)
  return none

/-- Detailed result from `provePreservedEqDetailed?`. -/
private structure PreservedEqResult where
  proof : Expr
  lhs : Expr
  rhs : Expr
  cleanRhs : Bool

/-- Prove `Independent writeLens getter`, handling `Lens.unit` explicitly without leaving
unconstrained universe metavariables on `PUnit`. -/
private def proveIndepSafe? (writeLens getter : Expr) : MetaM (Option Expr) := do
  let nl ← whnfOptic writeLens
  if nl.isAppOfArity ``Optic.Lens.unit 1 then
    let lTy ← whnf (← inferType nl)
    if lTy.isAppOfArity ``Optic.Lens 2 then
      let sTy := lTy.getArg! 0
      let aTy := lTy.getArg! 1
      let prf ← withLocalDeclD `x sTy fun xVar =>
        withLocalDeclD `v aTy fun vVar => do
          let gx ← mkAppM ``Optic.Getter.get #[getter, xVar]
          mkLambdaFVars #[xVar, vVar] (← mkEqRefl gx)
      let goalTy ← mkAppM ``Optic.Independent #[writeLens, getter]
      return some (← mkExpectedTypeHint prf goalTy)
  proveIndependent? writeLens getter

/-- Internal detailed version of `provePreservedEq?`, returning both the proof and whether any
`{ₗ s₀ with … }` updates on the RHS normalized cleanly. -/
private def provePreservedEqDetailed? (fh : FrameHyp) (getter : Expr) :
    MetaM (Option PreservedEqResult) := withDefault <| commitWhenSomeNoEx? do
  let getter ← instantiateMVars getter
  let hRaw? : Option Expr ← match fh.kind with
    | .rtModifies writeLens =>
      let some hind ← proveIndepSafe? writeLens getter | pure none
      some <$> mkAppM ``Optic.Modifies.rt_preserves #[hind, fh.proof]
    | .modifies writeLens =>
      let some hind ← proveIndepSafe? writeLens getter | pure none
      some <$> mkAppM ``Optic.Modifies.preserves #[hind, fh.proof]
    | .eqOn g₀ =>
      deriveFromGetterEq? g₀ fh.proof getter
    | .eqOnAll listExpr =>
      let some elems ← literalListElems? listExpr | pure none
      let listTy ← whnf (← inferType listExpr)
      if !listTy.isAppOfArity ``List 1 then
        pure none
      else
        let anyGetterTy := listTy.getArg! 0
        let mut found : Option Expr := none
        for idx in [0:elems.size] do
          let ag := elems[idx]!
          let g₀ ← extractAnyGetter ag
          let hMem ← mkListMemProof anyGetterTy ag listExpr idx
          let hMemEq ← mkAppM ``Optic.EqOnAll.of_mem #[fh.proof, hMem]
          if let some prf ← deriveFromGetterEq? g₀ hMemEq getter then
            found := some prf
            break
        pure found
    | .modifiesAny listExpr =>
      let some hall ← proveAllAnyLensIndep? listExpr getter | pure none
      some <$> mkAppM ``Optic.ModifiesAny.preserves #[hall, fh.proof]
    | .eqUpdate =>
      let getFn ← mkAppM ``Optic.Getter.get #[getter]
      some <$> mkCongrArg getFn fh.proof

  let some hRaw := hRaw? | return none
  let lhsPretty ← renderGetterApp getter fh.lhs
  let norm ← normalizeGetterOnUpdates getter fh.rhs
  let hCombined ← mkEqTrans hRaw norm.proof
  let expected ← mkEq lhsPretty norm.rhs
  let finalPrf ← mkExpectedTypeHint hCombined expected
  return some { proof := finalPrf, lhs := lhsPretty, rhs := norm.rhs, cleanRhs := norm.clean }

/-- Prove that `getter` is preserved by `fh`, normalizing any `{ₗ s₀ with … }` lens-update chain
on `fh.rhs` into clean field expressions (`st.pc = 16`, `st.data.regs.x0 = s₀.data.regs.x0 + 1`,
`st.data.dmem = s₀.data.dmem`). -/
def provePreservedEq? (fh : FrameHyp) (getter : Expr) : MetaM (Option Expr) := do
  return (← provePreservedEqDetailed? fh getter).map (·.proof)

/-- Split `writeLens` via `splitProdTree` and return the first factor `w` for which
`proveIndependent? w getter` fails, so error messages pinpoint the exact conflicting write lens. -/
def findConflictingWriteLens? (writeLens getter : Expr) : MetaM (Option Expr) := do
  let factors ← splitProdTree writeLens
  for w in factors do
    if (← proveIndependent? w getter).isNone then
      return some w
  if (← proveIndependent? writeLens getter).isNone then
    return some writeLens
  return none

/-! ### 3. Demand-Driven Discovery (`frameEqsFor`, `frameEqsInContext`) -/

/-- Generalization of `lensPathFromProj?` that works even when `sExpr` is a compound expression
rather than a free variable. -/
private def lensPathFromExpr? (sExpr : Expr) (stateType : Expr) (sub : Expr) :
    MetaM (Option Expr) := do
  if sExpr.isFVar then
    return ← lensPathFromProj? sExpr sub
  unless exprOccurs sExpr sub do return none
  withLocalDeclD `s stateType fun sVar => do
    let sub' := replaceExprExact sub sExpr sVar
    lensPathFromProj? sVar sub'

/-- Recognize an explicit optic application (`Getter.get`, `Iso.to`, `HasGet.getOf`, `^.`) out of
`sExpr` that may not reduce to a `Lens` (e.g., an arbitrary `Getter` or `Iso`). -/
private partial def getterFromOpticApp? (sExpr stateType sub : Expr) : MetaM (Option Expr) := do
  let sub := (← instantiateMVars sub).consumeMData
  if sub == sExpr then return none
  unless exprOccurs sExpr sub do return none

  -- First try `lensPathFromExpr?` (handles `.proj`, `S.field`, `Lens.get`, `Lens.view`, `fst`, `snd`)
  -- Note: map lookups are handled separately by the caller so we can attempt whole-map collapsing first.
  if let some lens ← lensPathFromExpr? sExpr stateType sub then
    let lWhnf ← whnfOptic lens
    unless lWhnf.isAppOfArity ``Optic.Lens.id 1 do
      return some (← mkAppM ``Optic.Lens.toGetter #[lens])

  -- `Optic.Getter.get g base`
  if sub.isAppOfArity ``Optic.Getter.get 4 then
    let g := sub.getArg! 2
    let base := sub.getArg! 3
    if !exprOccurs sExpr g then
      if base == sExpr then
        return some g
      if let some baseLens ← lensPathFromExpr? sExpr stateType base then
        if (← whnfOptic baseLens).isAppOfArity ``Optic.Lens.id 1 then
          return some g
        let baseG ← mkAppM ``Optic.Lens.toGetter #[baseLens]
        return some (← mkAppM ``Optic.Getter.comp #[baseG, g])

  -- `Optic.Iso.to i base`
  if sub.isAppOfArity ``Optic.Iso.to 4 then
    let iso := sub.getArg! 2
    let base := sub.getArg! 3
    if !exprOccurs sExpr iso then
      let isoG ← mkAppM ``Optic.Iso.toGetter #[iso]
      if base == sExpr then
        return some isoG
      if let some baseLens ← lensPathFromExpr? sExpr stateType base then
        if (← whnfOptic baseLens).isAppOfArity ``Optic.Lens.id 1 then
          return some isoG
        let baseG ← mkAppM ``Optic.Lens.toGetter #[baseLens]
        return some (← mkAppM ``Optic.Getter.comp #[baseG, isoG])

  -- `Optic.HasGet.getOf o base` / `Optic.Notation.viewOf base o`
  if sub.isAppOfArity ``Optic.Notation.viewOf 7 then
    if let some unfolded ← unfoldDefinition? sub then
      return ← getterFromOpticApp? sExpr stateType unfolded.headBeta
  if sub.isAppOfArity ``Optic.HasGet.getOf 6 then
    let o := sub.getArg! 4
    let base := sub.getArg! 5
    if !exprOccurs sExpr o then
      let oTy ← whnf (← inferType o)
      let oGetter? ←
        if oTy.isAppOfArity ``Optic.Getter 2 then pure (some o)
        else if oTy.isAppOfArity ``Optic.Lens 2 then some <$> mkAppM ``Optic.Lens.toGetter #[o]
        else if oTy.isAppOfArity ``Optic.Iso 2 then some <$> mkAppM ``Optic.Iso.toGetter #[o]
        else pure none
      if let some oG := oGetter? then
        if base == sExpr then
          return some oG
        if let some baseLens ← lensPathFromExpr? sExpr stateType base then
          if (← whnfOptic baseLens).isAppOfArity ``Optic.Lens.id 1 then
            return some oG
          let baseG ← mkAppM ``Optic.Lens.toGetter #[baseLens]
          return some (← mkAppM ``Optic.Getter.comp #[baseG, oG])
  return none

/-- Recognize a map lookup `fn arg` where `fn` projects a function `k → v` out of `sExpr`.
Returns `(baseLens, fn, arg, kTy, vTy, decInst)`. -/
private def recognizeMapLookup? (sExpr stateType sub : Expr) :
    MetaM (Option (Expr × Expr × Expr × Expr × Expr × Expr)) := do
  let .app fn arg := sub.consumeMData | return none
  unless exprOccurs sExpr fn do return none
  let some baseLens ← lensPathFromExpr? sExpr stateType fn | return none
  let fnTy ← whnf (← inferType fn)
  unless fnTy.isForall && !fnTy.bindingBody!.hasLooseBVars do return none
  let kTy := fnTy.bindingDomain!
  let vTy := fnTy.bindingBody!
  let some decInst := (← trySynthInstance (← mkAppM ``DecidableEq #[kTy])).toOption | return none
  return some (baseLens, fn, arg, kTy, vTy, decInst)

/-- Constants that should never be treated as derived user views `f s'`. -/
private def isIgnoredViewHead (env : Environment) (c : Name) : Bool :=
  c == ``Eq || c == ``HEq || c == ``Ne || c == ``Not || c == ``And || c == ``Or || c == ``Iff ||
  c == ``id || c == ``ite || c == ``dite || c == ``cond ||
  c == ``BEq.beq || c == ``bne || c == ``Decidable.decide ||
  c == ``Optic.Lens.get || c == ``Optic.Lens.set || c == ``Optic.Lens.over ||
  c == ``Optic.Lens.view || c == ``Optic.Lens.modifyF ||
  c == ``Optic.Getter.get || c == ``Optic.Iso.to || c == ``Optic.Iso.inv ||
  c == ``Optic.HasGet.getOf || c == ``Optic.Notation.viewOf ||
  c == ``Optic.Notation.setOf || c == ``Optic.Notation.overOf || c == ``Optic.Notation.pipe ||
  c == ``Optic.Modifies || c == ``Optic.ReflTransGen ||
  c == ``Optic.EqOn || c == ``Optic.EqOnAll || c == ``Optic.ModifiesAny ||
  (env.find? c).any fun info =>
    (match info with | .ctorInfo _ | .recInfo _ => true | _ => false) ||
    (match env.getProjectionFnInfo? c with | some _ => true | none => false)

/-- Recognize a named or local unary derived view applied directly to `sExpr` (such as
`MiniRegs.viewA r'`, `stateViewA st`, `stateViewMem a₂ st`, or `myView st a₂`). -/
private def derivedViewGetter? (sExpr stateType sub : Expr) : MetaM (Option Expr) := do
  let sub := sub.consumeMData
  unless sub.isApp do return none
  let fn := sub.getAppFn
  let args := sub.getAppArgs
  if exprOccurs sExpr fn then return none
  let env ← getEnv
  if let some c := fn.constName? then
    if isIgnoredViewHead env c then return none
  else unless fn.isFVar do
    return none

  -- Find whether `sExpr` appears directly as an argument, and no other argument mentions `sExpr`.
  let mut stateArgIdx? : Option Nat := none
  for i in [0:args.size] do
    let a := args[i]!.consumeMData
    if a == sExpr then
      if stateArgIdx?.isSome then return none
      stateArgIdx? := some i
    else if exprOccurs sExpr a then
      return none
  let some idx := stateArgIdx? | return none

  -- Must be Type-valued (not `Prop`), so `Getter S α` is well-typed.
  let subTy ← inferType sub
  unless ← isTypeValued subTy do return none

  -- Fast common case: `sExpr` is the last argument (`sub = mkApp prefixFn sExpr`).
  if idx == args.size - 1 then
    let prefixFn := sub.appFn!
    let pTy ← whnf (← inferType prefixFn)
    if pTy.isForall && !pTy.bindingBody!.hasLooseBVars then
      if ← isDefEq pTy.bindingDomain! stateType then
        return some (← mkAppM ``Optic.Getter.of #[prefixFn])

  -- General case: abstract `sExpr` as a lambda `fun s => fn a₀ … s … aₖ`.
  let viewFn ← withLocalDeclD `s stateType fun sVar => do
    let mut newArgs := args
    newArgs := newArgs.set! idx sVar
    let body := mkAppN fn newArgs
    mkLambdaFVars #[sVar] body
  return some (← mkAppM ``Optic.Getter.of #[viewFn])

/-- Choose a short readable suffix name for a getter (e.g., `"x0"`, `"dmem"`, `"pc"`,
`"stateViewA"`, `"viewA"`, `"dmem_a₂"`). -/
private partial def getterShortName (getter : Expr) : MetaM String := do
  let ng ← whnfOptic getter
  if ng.isAppOfArity ``Optic.Getter.of 3 then
    let f := (ng.getArg! 2).consumeMData
    if let some c := f.getAppFn.constName? then
      return c.getString!
    if f.isFVar then
      if let some decl := (← getLCtx).find? f.fvarId! then
        return decl.userName.toString
    if let .lam _ _ body _ := f then
      if let some c := body.getAppFn.constName? then
        return c.getString!
    return "view"
  if ng.isAppOfArity ``Optic.Lens.toGetter 3 then
    let l := ng.getArg! 2
    let segs ← splitCompChain l
    if segs.isEmpty then return "state"
    let last ← whnfOptic segs[segs.size - 1]!
    let env ← getEnv
    if let some c := last.getAppFn.constName? then
      if let some info := Optic.Derive.lookupLensField? env c then
        return info.fieldName.toString
    if last.isAppOfArity ``Optic.Lens.atKey 4 then
      let key := (last.getArg! 3).consumeMData
      let keyStr? : Option String ←
        if key.isFVar then
          match (← getLCtx).find? key.fvarId! with
          | some decl => pure (some decl.userName.toString)
          | none => pure none
        else if let some c := key.constName? then
          pure (some c.getString!)
        else if let some n := key.rawNatLit? then
          pure (some (toString n))
        else
          pure none
      let parentStr? : Option String ←
        if segs.size >= 2 then
          let prev ← whnfOptic segs[segs.size - 2]!
          if let some c := prev.getAppFn.constName? then
            if let some info := Optic.Derive.lookupLensField? env c then
              pure (some info.fieldName.toString)
            else pure (some c.getString!)
          else pure none
        else pure none
      match parentStr?, keyStr? with
      | some p, some k => return s!"{p}_{k}"
      | some p, none => return p
      | none, some k => return k
      | none, none => return "atKey"
    if last.isAppOfArity ``Optic.Lens.fst 2 then return "fst"
    if last.isAppOfArity ``Optic.Lens.snd 2 then return "snd"
    if let some c := last.getAppFn.constName? then
      return c.getString!
    if last.isFVar then
      if let some decl := (← getLCtx).find? last.fvarId! then
        return decl.userName.toString
    return "lens"
  if ng.isAppOfArity ``Optic.Iso.toGetter 3 then
    let i := ng.getArg! 2
    if let some c := i.getAppFn.constName? then
      return c.getString!
    return "iso"
  if ng.isAppOfArity ``Optic.Getter.comp 5 then
    return ← getterShortName (ng.getArg! 4)
  if ng.isAppOfArity ``Optic.Getter.map 5 then
    let f := (ng.getArg! 3).consumeMData
    if let some c := f.getAppFn.constName? then
      return c.getString!
    return ← getterShortName (ng.getArg! 4)
  if let some c := ng.getAppFn.constName? then
    return c.getString!
  return "eq"

/-- Prefix name derived from a `FrameHyp`'s proof FVar (defaults to `h`). -/
private def frameHypBaseName (fh : FrameHyp) : MetaM Name := do
  if fh.proof.isFVar then
    if let some decl := (← getLCtx).find? fh.proof.fvarId! then
      return decl.userName
  return `h

/-- Candidate equation collected during demand-driven discovery for a single `FrameHyp`. -/
private structure DiscoveredEq where
  fhIdx : Nat
  shortName : String
  baseName : Name
  proof : Expr
  eqType : Expr
  lensChain? : Option (Array Expr)
  cleanRhs : Bool
  deriving Inhabited

/-- Record a newly discovered preservation equation into `discoveredRef`. -/
private def recordDiscoveredEq (fhIdx : Nat) (fh : FrameHyp) (getter : Expr)
    (res : PreservedEqResult) (discoveredRef : IO.Ref (Array DiscoveredEq)) : MetaM Unit := do
  let eqType ← inferType res.proof
  let ng ← whnfOptic getter
  let lensChain? ←
    if ng.isAppOfArity ``Optic.Lens.toGetter 3 then
      some <$> splitCompChain (ng.getArg! 2)
    else
      pure none
  let shortName ← getterShortName getter
  let baseName ← frameHypBaseName fh
  discoveredRef.modify fun arr => arr.push {
    fhIdx, shortName, baseName, proof := res.proof, eqType, lensChain?, cleanRhs := res.cleanRhs
  }

/-- Top-down expression scanner discovering preserved projections, map lookups (with whole-map
collapsing), optic applications, and derived views referencing `fh.lhs`. -/
private partial def scanForFrameHyp (fhIdx : Nat) (fh : FrameHyp)
    (discoveredRef : IO.Ref (Array DiscoveredEq))
    (visitedRef : IO.Ref (Std.HashSet (Nat × Expr)))
    (boundFVars : Array FVarId) (e : Expr) : MetaM Unit := do
  let e := e.consumeMData
  unless exprOccurs fh.lhs e do return
  if e == fh.lhs then return
  -- Avoid exponential re-scanning on shared DAG subterms (only cache terms without local binders)
  if boundFVars.isEmpty then
    let key := (fhIdx, e)
    if (← visitedRef.get).contains key then return
    visitedRef.modify (·.insert key)

  let usesBound (t : Expr) : Bool :=
    !boundFVars.isEmpty && t.hasAnyFVar (fun fv => boundFVars.contains fv)

  -- 1. Map lookup `fn arg` where `fn` projects out of `fh.lhs`
  if let some (baseLens, fn, arg, kTy, vTy, decInst) ←
      recognizeMapLookup? fh.lhs fh.stateType e then
    let mut handledByWholeMap := false
    if !usesBound fn then
      let baseGetter ← mkAppM ``Optic.Lens.toGetter #[baseLens]
      if let some res ← provePreservedEqDetailed? fh baseGetter then
        if res.cleanRhs then
          recordDiscoveredEq fhIdx fh baseGetter res discoveredRef
          handledByWholeMap := true
    if !handledByWholeMap && !exprOccurs fh.lhs arg && !usesBound e then
      let keyLens ← mkAppOptM ``Optic.Lens.atKey #[some kTy, some vTy, some decInst, some arg]
      let fullLens ←
        if (← whnfOptic baseLens).isAppOfArity ``Optic.Lens.id 1 then pure keyLens
        else mkAppM ``Optic.Lens.comp #[baseLens, keyLens]
      let keyGetter ← mkAppM ``Optic.Lens.toGetter #[fullLens]
      if let some res ← provePreservedEqDetailed? fh keyGetter then
        recordDiscoveredEq fhIdx fh keyGetter res discoveredRef
    -- Always scan `arg` in case it independently mentions `fh.lhs`
    if exprOccurs fh.lhs arg then
      scanForFrameHyp fhIdx fh discoveredRef visitedRef boundFVars arg
    return

  -- 2. Projection chain or explicit optic application (`s'.a.b`, `l.get s'`, `s' ^. o`, …)
  if !usesBound e then
    if let some getter ← getterFromOpticApp? fh.lhs fh.stateType e then
      if let some res ← provePreservedEqDetailed? fh getter then
        recordDiscoveredEq fhIdx fh getter res discoveredRef
        return
      -- If the projection failed, don't descend into shorter prefixes of the same projection chain.
      if e.isProj then return
      if let some c := e.getAppFn.constName? then
        if (← getProjectionFnInfo? c).isSome then return

  -- 3. Named/local unary derived view `f … s'`
  if !usesBound e then
    if let some getter ← derivedViewGetter? fh.lhs fh.stateType e then
      if let some res ← provePreservedEqDetailed? fh getter then
        recordDiscoveredEq fhIdx fh getter res discoveredRef
        return

  -- 4. Recurse into subexpressions
  match e with
  | .app f a =>
    scanForFrameHyp fhIdx fh discoveredRef visitedRef boundFVars f
    scanForFrameHyp fhIdx fh discoveredRef visitedRef boundFVars a
  | .proj _ _ b =>
    scanForFrameHyp fhIdx fh discoveredRef visitedRef boundFVars b
  | .lam n dom body bi =>
    scanForFrameHyp fhIdx fh discoveredRef visitedRef boundFVars dom
    if body.hasLooseBVars then
      withLocalDecl n bi dom fun x =>
        scanForFrameHyp fhIdx fh discoveredRef visitedRef (boundFVars.push x.fvarId!) (body.instantiate1 x)
    else
      scanForFrameHyp fhIdx fh discoveredRef visitedRef boundFVars body
  | .forallE n dom body bi =>
    scanForFrameHyp fhIdx fh discoveredRef visitedRef boundFVars dom
    if body.hasLooseBVars then
      withLocalDecl n bi dom fun x =>
        scanForFrameHyp fhIdx fh discoveredRef visitedRef (boundFVars.push x.fvarId!) (body.instantiate1 x)
    else
      scanForFrameHyp fhIdx fh discoveredRef visitedRef boundFVars body
  | .letE n ty val body _ =>
    scanForFrameHyp fhIdx fh discoveredRef visitedRef boundFVars ty
    scanForFrameHyp fhIdx fh discoveredRef visitedRef boundFVars val
    if body.hasLooseBVars then
      withLetDecl n ty val fun x =>
        scanForFrameHyp fhIdx fh discoveredRef visitedRef (boundFVars.push x.fvarId!) (body.instantiate1 x)
    else
      scanForFrameHyp fhIdx fh discoveredRef visitedRef boundFVars body
  | .mdata _ inner =>
    scanForFrameHyp fhIdx fh discoveredRef visitedRef boundFVars inner
  | _ => pure ()

/-- Demand-driven scan of `exprs` for preserved subterms referencing the LHS of each frame
hypothesis in `hyps?` (defaults to `collectFrameHyps`).

Features:
- Discovers projection chains (`s'.a.b.c`), lens/getter/iso applications (`l.get s'`, `s' ^. l`),
  map lookups (`s'.data.dmem addr`), and derived views (`stateViewA st`, `stateViewMem a₂ st`).
- **Outermost-preserved-prefix collapsing**:
  - For map lookups `m addr`, emits ONE whole-map equation `m = …` whenever `m` is cleanly preserved
    as a whole, only descending to `atKey addr` when the map itself was partially modified.
  - When both `s'.a.b` (cleanly preserved) and a deeper `s'.a.b.c` appear for the same frame hyp,
    keeps only the outermost preserved prefix `s'.a.b`.
- Deduplicates by equality type up to reducible definitional equality and generates unique readable
  names (`h_x0`, `h_dmem`, `h_stateViewA`, `h_pc`, …). -/
def frameEqsFor (exprs : Array Expr) (hyps? : Option (Array FrameHyp) := none) :
    MetaM (Array (Name × Expr)) := do
  let hyps ← match hyps? with
    | some hs => pure hs
    | none => collectFrameHyps
  if hyps.isEmpty || exprs.isEmpty then
    return #[]

  let discoveredRef ← IO.mkRef (#[] : Array DiscoveredEq)
  let visitedRef ← IO.mkRef ({} : Std.HashSet (Nat × Expr))

  for fhIdx in [0:hyps.size] do
    let fh := hyps[fhIdx]!
    for expr in exprs do
      let expr ← instantiateMVars expr
      scanForFrameHyp fhIdx fh discoveredRef visitedRef #[] expr

  let allDisc ← discoveredRef.get

  -- Outermost-preserved-prefix collapsing: drop any candidate `b` whose lens path is strictly
  -- extended from another cleanly preserved candidate `a` of the same frame hypothesis.
  let mut collapsed : Array DiscoveredEq := #[]
  for i in [0:allDisc.size] do
    let cand := allDisc[i]!
    let mut subsumed := false
    if let some cChain := cand.lensChain? then
      for j in [0:allDisc.size] do
        if i == j then continue
        let other := allDisc[j]!
        if other.fhIdx == cand.fhIdx && other.cleanRhs then
          if let some oChain := other.lensChain? then
            if ← compChainIsStrictPrefix oChain cChain then
              subsumed := true
              break
    unless subsumed do
      collapsed := collapsed.push cand

  -- Deduplicate by equality type up to reducible defeq and assign unique hypothesis names.
  let mut dedupTypes : Array Expr := #[]
  let mut usedNames : Std.HashSet Name := {}
  let mut out : Array (Name × Expr) := #[]
  for cand in collapsed do
    let mut isDup := false
    for prevTy in dedupTypes do
      if ← withReducible (isDefEq prevTy cand.eqType) then
        isDup := true
        break
    if isDup then continue
    dedupTypes := dedupTypes.push cand.eqType
    let baseCand := cand.baseName.appendAfter ("_" ++ cand.shortName)
    let mut finalName := baseCand
    let mut suffix := 1
    while usedNames.contains finalName do
      finalName := baseCand.appendAfter (toString suffix)
      suffix := suffix + 1
    usedNames := usedNames.insert finalName
    out := out.push (finalName, cand.proof)
  return out

/-- Collect expressions from the main goal target and all non-implementation-detail local
declarations (optionally excluding one hypothesis FVar such as the frame hypothesis itself). -/
private def collectContextExprs (excludeFVar? : Option FVarId := none) : TacticM (Array Expr) :=
  withMainContext do
    let mut exprs : Array Expr := #[← instantiateMVars (← getMainTarget)]
    for decl in (← getLCtx) do
      if decl.isImplementationDetail then continue
      if excludeFVar? == some decl.fvarId then continue
      exprs := exprs.push (← instantiateMVars decl.type)
    return exprs

/-- Demand-driven frame preservation equalities extracted for all frame hypotheses in context
based on subterms occurring in the main target and local hypotheses (analogous to Kraken's
`frameEqsInContext`), propagating across multi-hop frame chains (`s₂ → s₁ → s₀`). -/
def frameEqsInContext : TacticM (Array Expr) := withMainContext do
  let hyps ← collectFrameHyps
  if hyps.isEmpty then return #[]
  let mut all : Array Expr := #[]
  let mut seenTypes : Array Expr := #[]
  let mut extraExprs : Array Expr := #[]
  for _ in [0:hyps.size] do
    let mut addedThisRound := false
    let mut newExprs : Array Expr := #[]
    for fh in hyps do
      let exclude? := if fh.proof.isFVar then some fh.proof.fvarId! else none
      let exprs := (← collectContextExprs exclude?) ++ extraExprs
      let eqs ← frameEqsFor exprs (some #[fh])
      for (_, prf) in eqs do
        let ty ← inferType prf
        let mut dup := false
        for prevTy in seenTypes do
          if ← withReducible (isDefEq prevTy ty) then
            dup := true
            break
        unless dup do
          seenTypes := seenTypes.push ty
          all := all.push prf
          newExprs := newExprs.push ty
          addedThisRound := true
    if !addedThisRound then break
    extraExprs := extraExprs ++ newExprs
  return all

/-! ### 4. Explicit Target Resolution for `lens_eqs h [p₁, p₂, …]` -/

/-- Resolve a dot-separated field path `a.b.c` starting from `sTy` using `make_lenses` lenses. -/
private def resolveDotLensPath? (sTy : Expr) (stx : Term) : TermElabM (Option Expr) := do
  unless stx.raw.isIdent do return none
  let segs := stx.raw.getId.components
  if segs.isEmpty then return none
  let saved ← saveState
  try
    let mut curTy ← instantiateMVars sTy
    let mut acc : Option Expr := none
    for seg in segs do
      let curTyWhnf ← whnf curTy
      let .const typeName _ := curTyWhnf.getAppFn | saved.restore; return none
      let lensName := typeName ++ `Lenses ++ seg
      unless (← getEnv).contains lensName do
        saved.restore
        return none
      let stepLens ← mkAppOptM lensName (curTyWhnf.getAppArgs.map some)
      let stepTy ← whnf (← inferType stepLens)
      unless stepTy.isAppOfArity ``Optic.Lens 2 do
        saved.restore
        return none
      acc ← match acc with
        | none => pure (some stepLens)
        | some prev => pure (some (← mkAppM ``Optic.Lens.comp #[prev, stepLens]))
      curTy ← instantiateMVars (stepTy.getArg! 1)
    return acc
  catch _ =>
    saved.restore
    return none

/-- Elaborate a single explicit target `p` in `lens_eqs h [p₁, p₂, …]` into a `Getter sTy _`
(accepting dot-paths, `Lens`, `Getter`, `Iso`, `AnyGetter`, or plain functions `sTy → α`). -/
private def elabTargetGetter (sTy : Expr) (p : Term) : TermElabM Expr := do
  -- 1. Try `make_lenses` dot-path first (`data.regs.x0`, `pc`, `data.dmem`)
  if let some lens ← resolveDotLensPath? sTy p then
    return ← mkAppM ``Optic.Lens.toGetter #[lens]
  -- 2. Otherwise elaborate as a Lean term
  let e ← instantiateMVars (← Term.elabTerm p none)
  let eTy ← whnf (← instantiateMVars (← inferType e))
  if eTy.isAppOfArity ``Optic.Getter 2 then
    return e
  if eTy.isAppOfArity ``Optic.Lens 2 then
    return ← mkAppM ``Optic.Lens.toGetter #[e]
  if eTy.isAppOfArity ``Optic.Iso 2 then
    return ← mkAppM ``Optic.Iso.toGetter #[e]
  if eTy.isAppOfArity ``Optic.AnyGetter 1 then
    return ← extractAnyGetter e
  if eTy.isForall && !eTy.bindingBody!.hasLooseBVars then
    if ← isDefEq eTy.bindingDomain! sTy then
      return ← mkAppM ``Optic.Getter.of #[e]
  throwErrorAt p
    "lens_eqs: expected a dot-path, `Lens`, `Getter`, `Iso`, or function `{sTy} → _`, got `{p}` of type:{indentExpr eTy}"

/-- Fallback extraction of all explicitly listed members for `EqOn` / `EqOnAll` when demand-driven
discovery finds no references in the goal or context. -/
private def fallbackEqOnMembers (fh : FrameHyp) : MetaM (Array (Name × Expr)) := do
  let baseName ← frameHypBaseName fh
  let mut out : Array (Name × Expr) := #[]
  let mut usedNames : Std.HashSet Name := {}
  let pushItem (getter : Expr) (prf : Expr) (out : Array (Name × Expr))
      (usedNames : Std.HashSet Name) : MetaM (Array (Name × Expr) × Std.HashSet Name) := do
    let shortName ← getterShortName getter
    let baseCand := baseName.appendAfter ("_" ++ shortName)
    let mut finalName := baseCand
    let mut suffix := 1
    while usedNames.contains finalName do
      finalName := baseCand.appendAfter (toString suffix)
      suffix := suffix + 1
    return (out.push (finalName, prf), usedNames.insert finalName)
  match fh.kind with
  | .eqOn g =>
    if let some prf ← provePreservedEq? fh g then
      let (out', _) ← pushItem g prf out usedNames
      return out'
    return #[]
  | .eqOnAll listExpr =>
    let some elems ← literalListElems? listExpr | return #[]
    for ag in elems do
      let g ← extractAnyGetter ag
      if let some prf ← provePreservedEq? fh g then
        (out, usedNames) ← pushItem g prf out usedNames
    return out
  | _ => return #[]

/-! ### 5. User-Facing `lens_eqs` Tactic -/

/-- Demand-driven forward extraction of preserved equations from frame hypotheses:
- `lens_eqs h`: scans the goal and context for projections, map lookups, and derived views of `h`'s
  LHS state and asserts only the referenced preserved equations (`h_x0`, `h_pc`, `h_dmem`, …).
- `lens_eqs h [p₁, p₂, …]`: extracts specific dot-paths, `Lens`/`Getter`/`Iso` expressions, or
  derived views, reporting the conflicting write lens if any target is not preserved.
- `lens_eqs`: runs demand-driven extraction across all frame hypotheses in context. -/
syntax (name := lensEqs) "lens_eqs" (ppSpace colGt ident (" [" term,* "]")?)? : tactic

elab_rules : tactic
  | `(tactic| lens_eqs) => withMainContext do
    let hyps ← collectFrameHyps
    if hyps.isEmpty then
      throwError "lens_eqs: no frame hypotheses (`ReflTransGen (Modifies _)`, `Modifies`, `EqOn`, `EqOnAll`) in context"
    let mut toAssert : Array Hypothesis := #[]
    let mut seenTypes : Array Expr := #[]
    let mut usedNames : Std.HashSet Name := {}
    let mut extraExprs : Array Expr := #[]
    for _ in [0:hyps.size] do
      let mut addedThisRound := false
      let mut newExprs : Array Expr := #[]
      for fh in hyps do
        let exclude? := if fh.proof.isFVar then some fh.proof.fvarId! else none
        let exprs := (← collectContextExprs exclude?) ++ extraExprs
        let eqs ← frameEqsFor exprs (some #[fh])
        for (nm, prf) in eqs do
          let ty ← inferType prf
          let mut dup := false
          for prevTy in seenTypes do
            if ← withReducible (isDefEq prevTy ty) then dup := true; break
          if dup then continue
          seenTypes := seenTypes.push ty
          let mut finalName := nm
          let mut suffix := 1
          while usedNames.contains finalName do
            finalName := nm.appendAfter (toString suffix)
            suffix := suffix + 1
          usedNames := usedNames.insert finalName
          toAssert := toAssert.push { userName := finalName, type := ty, value := prf }
          newExprs := newExprs.push ty
          addedThisRound := true
      if !addedThisRound then break
      extraExprs := extraExprs ++ newExprs
    if toAssert.isEmpty then
      throwError "lens_eqs: no referenced preserved subterms found in goal or context"
    let (_, g) ← (← getMainGoal).assertHypotheses toAssert
    replaceMainGoal [g]

  | `(tactic| lens_eqs $h:ident $[[$targets?:term,*]]?) => withMainContext do
    let some decl := (← getLCtx).findFromUserName? h.getId
      | throwErrorAt h "lens_eqs: unknown hypothesis `{h}`"
    let some fh ← parseFrameHyp? decl.toExpr
      | throwErrorAt h
          "lens_eqs: `{h}` is not a recognized frame hypothesis (`ReflTransGen (Modifies _)`, `Modifies`, `EqOn`, `EqOnAll`, `ModifiesAny`, or `is \{ … with … }`)"
    match targets? with
    | some ts =>
      let mut toAssert : Array Hypothesis := #[]
      let mut usedNames : Std.HashSet Name := {}
      for p in ts.getElems do
        let getter ← elabTargetGetter fh.stateType p
        match ← provePreservedEq? fh getter with
        | some prf =>
          let shortName ← getterShortName getter
          let baseCand := h.getId.appendAfter ("_" ++ shortName)
          let mut finalName := baseCand
          let mut suffix := 1
          while usedNames.contains finalName do
            finalName := baseCand.appendAfter (toString suffix)
            suffix := suffix + 1
          usedNames := usedNames.insert finalName
          toAssert := toAssert.push {
            userName := finalName
            type := ← inferType prf
            value := prf
          }
        | none =>
          match fh.kind with
          | .rtModifies writeLens | .modifies writeLens =>
            if let some conflict ← findConflictingWriteLens? writeLens getter then
              throwErrorAt p
                "lens_eqs: `{p}` is not preserved by `{h}`: conflicts with write lens:{indentExpr conflict}"
            else
              throwErrorAt p
                "lens_eqs: `{p}` is not preserved by `{h}` (write lens:{indentExpr writeLens})"
          | .eqOn g₀ =>
            throwErrorAt p
              "lens_eqs: `{p}` is not preserved by `{h}` (only preserves:{indentExpr g₀})"
          | .eqOnAll listExpr =>
            throwErrorAt p
              "lens_eqs: `{p}` is not preserved by `{h}` (only preserves:{indentExpr listExpr})"
          | .modifiesAny listExpr =>
            throwErrorAt p
              "lens_eqs: `{p}` is not preserved by `{h}` (modifies:{indentExpr listExpr})"
          | .eqUpdate =>
            throwErrorAt p "lens_eqs: failed to extract `{p}` from `{h}`"
      let (_, g) ← (← getMainGoal).assertHypotheses toAssert
      replaceMainGoal [g]
    | none =>
      let exprs ← collectContextExprs (some decl.fvarId)
      let mut eqs ← frameEqsFor exprs (some #[fh])
      if eqs.isEmpty then
        eqs ← fallbackEqOnMembers fh
      if eqs.isEmpty then
        throwErrorAt h "lens_eqs: no referenced preserved subterms for `{h}` found in goal or context"
      let toAssert ← eqs.mapM fun (nm, prf) => do
        pure { userName := nm, type := ← inferType prf, value := prf : Hypothesis }
      let (_, g) ← (← getMainGoal).assertHypotheses toAssert
      replaceMainGoal [g]

/-! ### 6. Demand-Driven Frame-Rewriting Simproc & `lens_rw` Tactic -/

/-- Filter frame hypotheses into an acyclic DAG of directed state transitions `lhs → base(rhs)`,
skipping self-loops and back-edges so `lens_rw` can never enter a rewrite cycle. -/
private def filterAcyclicFrameHyps (hyps : Array FrameHyp) (excludeFVar? : Option FVarId := none) :
    MetaM (Array FrameHyp) := do
  let mut accepted : Array FrameHyp := #[]
  let mut edges : Array (Expr × Expr) := #[]
  let isReachable (edges : Array (Expr × Expr)) (src dst : Expr) : Bool := Id.run do
    if src == dst then return true
    let mut stack : Array Expr := #[src]
    let mut seen : Std.HashSet Expr := {}
    while !stack.isEmpty do
      let cur := stack.back!
      stack := stack.pop
      if seen.contains cur then continue
      seen := seen.insert cur
      for (u, v) in edges do
        if u == cur then
          if v == dst then return true
          if !seen.contains v then
            stack := stack.push v
    return false
  for fh in hyps do
    if let some excl := excludeFVar? then
      if fh.proof.containsFVar excl then continue
    let base ← baseStateOfUpdates fh.rhs
    if fh.lhs == base then continue
    -- Skip if adding `fh.lhs → base` would create a cycle (`base` already reaches `fh.lhs`)
    if isReachable edges base fh.lhs then continue
    accepted := accepted.push fh
    edges := edges.push (fh.lhs, base)
  return accepted

/-- Try to rewrite expression `e` one step using the active DAG of frame hypotheses.
When `isPre = true`, defers map lookups `m addr` whose map `m` is cleanly preserved as a whole
so `Simp` rewrites `m` and `addr` first. -/
private def tryFrameRwOneStep (hyps : Array FrameHyp) (visitedRef : IO.Ref (Std.HashSet Expr))
    (isPre : Bool) (e : Expr) : MetaM Simp.Step := withDefault do
  let eClean := e.consumeMData
  if (← visitedRef.get).contains eClean then
    return .continue
  for fh in hyps do
    unless exprOccurs fh.lhs eClean && eClean != fh.lhs do continue
    let rhsIsUpdate := (← peelLensUpdate? fh.rhs).isSome

    -- Helper to finalize a rewrite `e ↦ targetRhs` with cycle guard and defeq proof check
    let finishRw (res : PreservedEqResult) : MetaM (Option Simp.Step) := do
      let targetRhs ←
        if rhsIsUpdate then
          pure res.rhs
        else
          -- Preserve the exact syntactic form of `e` (e.g. `^.` vs `.field`) when rewriting
          -- `s' ↦ s` across a plain frame edge.
          let replaced := replaceExprExact eClean fh.lhs fh.rhs
          if ← isDefEq replaced res.rhs then pure replaced else pure res.rhs
      if targetRhs == eClean then return none
      if (← visitedRef.get).contains targetRhs then return none
      let expected ← mkEq e targetRhs
      unless ← isDefEq (← inferType res.proof) expected do return none
      let prf ← mkExpectedTypeHint res.proof expected
      visitedRef.modify (·.insert eClean)
      return some (.visit { expr := targetRhs, proof? := some prf })

    -- 1. Map lookup `fn arg`
    if let some (baseLens, _, arg, kTy, vTy, decInst) ←
        recognizeMapLookup? fh.lhs fh.stateType eClean then
      if isPre then
        let baseGetter ← mkAppM ``Optic.Lens.toGetter #[baseLens]
        if let some res ← provePreservedEqDetailed? fh baseGetter then
          if res.cleanRhs then
            -- Let `Simp` descend into `fn` and `arg` first
            return .continue
      if !exprOccurs fh.lhs arg then
        let keyLens ← mkAppOptM ``Optic.Lens.atKey #[some kTy, some vTy, some decInst, some arg]
        let fullLens ←
          if (← whnfOptic baseLens).isAppOfArity ``Optic.Lens.id 1 then pure keyLens
          else mkAppM ``Optic.Lens.comp #[baseLens, keyLens]
        let keyGetter ← mkAppM ``Optic.Lens.toGetter #[fullLens]
        if let some res ← provePreservedEqDetailed? fh keyGetter then
          if let some step ← finishRw res then
            return step
      continue

    -- 2. Projection chain or explicit optic application
    if let some getter ← getterFromOpticApp? fh.lhs fh.stateType eClean then
      if let some res ← provePreservedEqDetailed? fh getter then
        -- When `fh.rhs` is a `{ₗ … with … }` update chain and `getter` didn't peel cleanly,
        -- don't rewrite a whole sub-struct (like `st.data.regs`) into `{ … }.data.regs` during `pre`,
        -- so `Simp` can descend to inner fields (`st.data.regs.x0`) that DO peel cleanly!
        if !rhsIsUpdate || res.cleanRhs then
          if let some step ← finishRw res then
            return step
      continue

    -- 3. Named / local unary derived view `f … s'`
    if let some getter ← derivedViewGetter? fh.lhs fh.stateType eClean then
      if let some res ← provePreservedEqDetailed? fh getter then
        if !rhsIsUpdate || res.cleanRhs then
          if let some step ← finishRw res then
            return step
  return .continue

/-- Build `(preSimproc, postSimproc)` for demand-driven frame rewriting across `hyps`.
Chains transitively across `s₂ → s₁ → s₀` in a single `Simp.main` pass with cycle avoidance. -/
def mkFrameRwSimprocs (hyps : Array FrameHyp) (excludeFVar? : Option FVarId := none) :
    MetaM (Simp.Simproc × Simp.Simproc) := do
  let active ← filterAcyclicFrameHyps hyps excludeFVar?
  let visitedRef ← IO.mkRef ({} : Std.HashSet Expr)
  let pre : Simp.Simproc := fun e => do
    tryFrameRwOneStep active visitedRef true e
  let post : Simp.Simproc := fun e => do
    tryFrameRwOneStep active visitedRef false e
  return (pre, post)

/-- Build custom `Simp.Methods` combining `baseMethods` with demand-driven frame rewriting across
`hyps`. Downstream tactics (such as `lens_simp`) can pass these directly to `Simp.main`. -/
def mkFrameRwMethods (hyps : Array FrameHyp) (excludeFVar? : Option FVarId := none)
    (baseMethods : Simp.Methods := Simp.mkDefaultMethodsCore #[]) : MetaM Simp.Methods := do
  let (preProc, postProc) ← mkFrameRwSimprocs hyps excludeFVar?
  return { baseMethods with
    pre := fun e => do
      match ← preProc e with
      | .continue none => baseMethods.pre e
      | step => return step
    post := fun e => do
      match ← postProc e with
      | .continue none => baseMethods.post e
      | step => return step
  }

/-- Rewrite an expression `e` using demand-driven frame preservation across `hyps` (without running
the global `@[simp]` set). Returns `some (e', proof)` iff `e` changed. -/
def frameRwExpr (e : Expr) (hyps : Array FrameHyp) (excludeFVar? : Option FVarId := none) :
    MetaM (Option (Expr × Expr)) := do
  let e ← instantiateMVars e
  let active ← filterAcyclicFrameHyps hyps excludeFVar?
  if active.isEmpty then return none
  let ctx ← Simp.mkContext
    { decide := false, iota := false, zeta := false, zetaDelta := false, beta := false, eta := false }
    (simpTheorems := #[])
    (congrTheorems := ← getSimpCongrTheorems)
  let methods ← mkFrameRwMethods active none
  let (res, _) ← Simp.main e ctx (methods := methods)
  if res.expr == e then
    return none
  return some (res.expr, ← res.getProof)

/-- Demand-driven frame rewriting (`lens_rw`, `lens_rw at h₁ h₂`, `lens_rw at *`).
Rewrites preserved projections, map lookups, and derived views across all frame hypotheses in
context — chaining transitively (`s₂ → s₁ → s₀`) in one sweep without polluting the local context. -/
syntax (name := lensRw) "lens_rw" (Lean.Parser.Tactic.location)? : tactic

elab_rules : tactic
  | `(tactic| lens_rw $[$loc?]?) => withMainContext do
    let loc := match loc? with
      | none => Location.targets #[] true
      | some l => expandLocation l

    let mut curGoal ← getMainGoal
    let mut changed := false

    let rwHyp (g : MVarId) (fv : FVarId) : MetaM (MVarId × FVarSubst × Bool) := g.withContext do
      let decl ← fv.getDecl
      if decl.isImplementationDetail || decl.hasValue then
        return (g, {}, false)
      let hyps ← collectFrameHyps
      let ty ← instantiateMVars decl.type
      match ← frameRwExpr ty hyps (some fv) with
      | some (tyNew, prf) =>
        let res ← g.replaceLocalDecl fv tyNew prf
        return (res.mvarId, res.subst, true)
      | none =>
        return (g, {}, false)

    let rwTarget (g : MVarId) : MetaM (Option MVarId × Bool) := g.withContext do
      let hyps ← collectFrameHyps
      let tgt ← instantiateMVars (← g.getType)
      match ← frameRwExpr tgt hyps none with
      | some (tgtNew, prf) =>
        let g' ← g.replaceTargetEq tgtNew prf
        let closed ← commitWhen do
          try g'.refl; return true catch _ => return false
        if closed then
          return (none, true)
        return (some g', true)
      | none =>
        return (some g, false)

    match loc with
    | .wildcard =>
      let fvars ← curGoal.withContext do
        let mut arr : Array FVarId := #[]
        for decl in (← getLCtx) do
          if decl.isImplementationDetail || decl.hasValue then continue
          arr := arr.push decl.fvarId
        return arr
      let mut substs : Array FVarSubst := #[]
      for fv in fvars do
        let fv' := match substs.foldl (fun e s => s.apply e) (mkFVar fv) with
          | .fvar id => id
          | _ => fv
        let existsInCtx ← curGoal.withContext do
          return ((← getLCtx).find? fv').isSome
        if existsInCtx then
          let (g', s', ch) ← rwHyp curGoal fv'
          curGoal := g'
          if ch then
            changed := true
            substs := substs.push s'
      let (gOpt, chT) ← rwTarget curGoal
      if chT then changed := true
      unless changed do
        throwError "lens_rw: no preserved frame subterms to rewrite"
      match gOpt with
      | none => replaceMainGoal []
      | some gFinal => replaceMainGoal [gFinal]

    | .targets hypStxs simplifyTarget =>
      let fvars ← curGoal.withContext do
        let mut arr : Array FVarId := #[]
        for stx in hypStxs do
          let some decl := (← getLCtx).findFromUserName? stx.getId
            | throwErrorAt stx "lens_rw: unknown hypothesis `{stx}`"
          arr := arr.push decl.fvarId
        return arr
      let mut substs : Array FVarSubst := #[]
      for fv in fvars do
        let fv' := match substs.foldl (fun e s => s.apply e) (mkFVar fv) with
          | .fvar id => id
          | _ => fv
        let (g', s', ch) ← rwHyp curGoal fv'
        curGoal := g'
        if ch then
          changed := true
          substs := substs.push s'
      if simplifyTarget then
        let (gOpt, chT) ← rwTarget curGoal
        if chT then changed := true
        unless changed do
          throwError "lens_rw: no preserved frame subterms to rewrite"
        match gOpt with
        | none => replaceMainGoal []
        | some gFinal => replaceMainGoal [gFinal]
      else
        unless changed do
          throwError "lens_rw: no preserved frame subterms to rewrite"
        replaceMainGoal [curGoal]

end Optic.Tactic

end
