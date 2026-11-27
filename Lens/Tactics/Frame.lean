module

public import Lens.Basic
public import Lens.Relation
public import Lens.Frame
public import Lens.ProdFrame
public import Lens.Derive
public import Lens.ExtraNotation
public import Lens.Tactics.Disjoint
public meta import Lean

/-!
# Generic Lens Framing Automation (`lens_frame`)

Architecture-independent framing tactic for `Optic` built purely on `Lens`, `Getter`,
`Modifies`, `FactorsLawful`, `ReflTransGen`, `EqOn`, and `EqOnAll`:

- `isFrameGoal`: recognizes `ReflTransGen (Modifies _) _ _`, `Modifies _ _ _`, `EqOn _ _ _`,
  and `EqOnAll _ _ _`.
- **Engine A (Symbolic State-Update Diff)**: diffs concrete lens updates (`l.set`, `l.over`,
  `{ₗ s with … }`) and raw Lean structure updates/constructors (`{ s with … }`, `S.mk …`),
  using a 1-step witness-tuple fast path (`ReflTransGen.single ⟨w, rfl⟩`), falling back to
  per-field compositional chains with substate lifting and missing-write diagnostics
  (`lens_frame: add to writes: [...]` + focused equality subgoals).
- **Engine B (Context Frame-Algebra Graph Search)**: builds a state graph from local `Eq`,
  `let`, `Modifies`, `ReflTransGen (Modifies _)`, concrete updates, and lifted substate
  frames (`Modifies.rt_lift` / `Modifies.lift`); finds a path via BFS supporting arbitrary
  permutation, weakening, deduplication, symmetry, and hierarchical coarsening
  (`Modifies.coarsen`) with zero `Disjoint` obligations under `ReflTransGen`.
- **Engine C (Preservation & Narrowing)**: discharges `EqOn` and `EqOnAll` (`≡ₚ … on […]`)
  by splitting `EqOnAll.cons` / `EqOnAll.nil`, trying `with_reducible rfl`, and walking the
  state graph via `proveIndependent?` + `Modifies.rt_preserves` / `Modifies.preserves`,
  leaving any unproved getter subgoals open.
-/

public meta section

open Lean Meta Elab Tactic

namespace Optic.Tactic

/-! ### 1. Goal Recognition & Core Lens Utilities -/

/-- Match `Optic.Modifies L` (possibly eta-expanded), returning `(stateTy, L)`. -/
private def matchModifiesRel? (r : Expr) : Option (Expr × Expr) :=
  let r := r.consumeMData
  if r.isAppOfArity ``Optic.Modifies 3 then
    some (r.getArg! 0, r.getArg! 2)
  else match r with
  | .lam _ _ (.lam _ _ body _) _ =>
    let body := body.consumeMData
    if body.isAppOfArity ``Optic.Modifies 5 &&
        body.getArg! 3 == .bvar 1 && body.getArg! 4 == .bvar 0 &&
        !(body.getArg! 2).hasLooseBVars then
      some (body.getArg! 0, body.getArg! 2)
    else
      none
  | _ => none

/-- Match `ReflTransGen (Modifies L) s' s`, returning `(stateTy, L, s', s)`. -/
private def matchRtModifies? (e : Expr) : Option (Expr × Expr × Expr × Expr) :=
  let e := e.consumeMData
  if e.isAppOfArity ``Optic.ReflTransGen 4 then
    match matchModifiesRel? (e.getArg! 1) with
    | some (sTy, l) => some (sTy, l, e.getArg! 2, e.getArg! 3)
    | none => none
  else
    none

/-- Match `Modifies L s' s`, returning `(stateTy, L, s', s)`. -/
private def matchModifies? (e : Expr) : Option (Expr × Expr × Expr × Expr) :=
  let e := e.consumeMData
  if e.isAppOfArity ``Optic.Modifies 5 then
    some (e.getArg! 0, e.getArg! 2, e.getArg! 3, e.getArg! 4)
  else
    none

/-- Match `EqOn g s' s`, returning `(stateTy, g, s', s)`. -/
private def matchEqOn? (e : Expr) : Option (Expr × Expr × Expr × Expr) :=
  let e := e.consumeMData
  if e.isAppOfArity ``Optic.EqOn 5 then
    some (e.getArg! 0, e.getArg! 2, e.getArg! 3, e.getArg! 4)
  else
    none

/-- Match `EqOnAll gs s' s`, returning `(stateTy, gs, s', s)`. -/
private def matchEqOnAll? (e : Expr) : Option (Expr × Expr × Expr × Expr) :=
  let e := e.consumeMData
  if e.isAppOfArity ``Optic.EqOnAll 4 then
    some (e.getArg! 0, e.getArg! 1, e.getArg! 2, e.getArg! 3)
  else
    none

/-- Recognize lens framing goals:
`ReflTransGen (Modifies _) _ _`, `Modifies _ _ _`, `EqOn _ _ _`, and `EqOnAll _ _ _`. -/
def isFrameGoal (e : Expr) : Bool :=
  (matchRtModifies? e).isSome ||
  (matchModifies? e).isSome ||
  (matchEqOn? e).isSome ||
  (matchEqOnAll? e).isSome

/-- Construct `Optic.Lens.unit.{u, 0} (s := sTy)` with no dangling universe metavariables. -/
private def mkUnitLens (sTy : Expr) : MetaM Expr := do
  let u ← mkFreshLevelMVar
  let sort ← inferType sTy
  unless ← isDefEq sort (mkSort (.succ u)) do
    throwError "mkUnitLens: expected a Type, got:{indentExpr sTy}"
  let u ← instantiateLevelMVars u
  return mkApp (mkConst ``Optic.Lens.unit [u, Level.zero]) sTy

/-- Build a right-associated `Lens.prod` tree from a non-empty array of lenses. -/
private def mkProdTree (lenses : Array Expr) : MetaM Expr := do
  if lenses.isEmpty then
    throwError "mkProdTree: empty lens array"
  let mut acc := lenses[lenses.size - 1]!
  for i in [1:lenses.size] do
    let idx := lenses.size - 1 - i
    acc ← mkAppM ``Optic.Lens.prod #[lenses[idx]!, acc]
  return acc

/-- Synthesize `FactorsLawful l`, retrying on `whnfOptic l` if needed. -/
partial def synthFactorsLawful? (l : Expr) : MetaM (Option Expr) := do
  let l ← instantiateMVars l
  let ty ← mkAppM ``Optic.FactorsLawful #[l]
  if let some inst := (← trySynthInstance ty).toOption then
    return some inst
  let nl ← whnfOptic l
  if nl != l then
    let ty' ← mkAppM ``Optic.FactorsLawful #[nl]
    if let some inst := (← trySynthInstance ty').toOption then
      return some (← mkExpectedTypeHint inst ty)
  return none

/-- Prove `LawfulLens l` via typeclass synthesis, or recursively via `Lens.lawful_prod` +
`proveDisjoint?` and `Lens.lawful_comp`. -/
partial def proveLawfulLens? (l : Expr) (fuel : Nat := 16) : MetaM (Option Expr) := do
  if fuel == 0 then return none
  let l ← instantiateMVars l
  if let some inst ← synthLawfulLens? l then
    return some inst
  let goalTy ← mkAppM ``Optic.LawfulLens #[l]
  let nl ← whnfOptic l
  if nl != l then
    if let some inst ← synthLawfulLens? nl then
      return some (← mkExpectedTypeHint inst goalTy)
  if nl.isAppOfArity ``Optic.Lens.prod 5 then
    let l₁ := nl.getArg! 3
    let l₂ := nl.getArg! 4
    if let some h₁ ← proveLawfulLens? l₁ (fuel - 1) then
      if let some h₂ ← proveLawfulLens? l₂ (fuel - 1) then
        if let some hdisj ← proveDisjoint? l₁ l₂ then
          let prf ← mkAppOptM ``Optic.Lens.lawful_prod
            #[none, none, none, some l₁, some l₂, some h₁, some h₂, some hdisj]
          return some (← mkExpectedTypeHint prf goalTy)
  if nl.isAppOfArity ``Optic.Lens.comp 5 then
    let outer := nl.getArg! 3
    let inner := nl.getArg! 4
    if let some h₁ ← proveLawfulLens? outer (fuel - 1) then
      if let some h₂ ← proveLawfulLens? inner (fuel - 1) then
        let prf ← mkAppOptM ``Optic.Lens.lawful_comp
          #[none, none, none, some outer, some inner, some h₁, some h₂]
        return some (← mkExpectedTypeHint prf goalTy)
  return none

/-- Synthesize `LawfulIso i` if possible. -/
private def synthLawfulIso? (i : Expr) : MetaM (Option Expr) := do
  let ty ← mkAppM ``Optic.LawfulIso #[i]
  return (← trySynthInstance ty).toOption

/-- Format a lens composition chain as a human-readable dot-path (e.g., `data.regs.x1`, `pc`). -/
private def formatLensPath (l : Expr) : MetaM String := do
  let segs ← splitCompChain l
  if segs.isEmpty then return "id"
  let env ← getEnv
  let mut parts : Array String := #[]
  for seg in segs do
    let seg ← whnfOptic seg
    if let some c := seg.getAppFn.constName? then
      if let some info := Optic.Derive.lookupLensField? env c then
        parts := parts.push info.fieldName.toString
        continue
    if seg.isAppOfArity ``Optic.Lens.fst 2 then
      parts := parts.push "1"
    else if seg.isAppOfArity ``Optic.Lens.snd 2 then
      parts := parts.push "2"
    else if seg.isAppOfArity ``Optic.Lens.atKey 4 then
      let kStr := (toString (← ppExpr (seg.getArg! 3))).replace "\n" " "
      parts := parts.push s!"atKey({kStr})"
    else
      let s := (toString (← ppExpr seg)).replace "\n" " "
      parts := parts.push s
  return ".".intercalate parts.toList

/-- Normalize top-level `Notation.viewOf` / `HasGet.getOf` / `Lens.view` into `Lens.get` /
`Getter.get` / `Iso.to` without unfolding opaque lens definitions like `low8` or `atKey`. -/
private def normalizeOpticView (e : Expr) : MetaM Expr := do
  let mut cur := (← instantiateMVars e).consumeMData.headBeta
  if cur.isAppOfArity ``Optic.Notation.viewOf 6 then
    if let some cur' ← unfoldDefinition? cur then
      cur := cur'.consumeMData.headBeta
  if cur.isAppOfArity ``Optic.HasGet.getOf 6 then
    let o := cur.getArg! 4
    let x := cur.getArg! 5
    let oTy ← whnf (← inferType o)
    if oTy.isAppOfArity ``Optic.Lens 2 then
      let cand ← mkAppM ``Optic.Lens.get #[o, x]
      if ← isDefEq cur cand then return cand
    else if oTy.isAppOfArity ``Optic.Getter 2 then
      let cand ← mkAppM ``Optic.Getter.get #[o, x]
      if ← isDefEq cur cand then return cand
    else if oTy.isAppOfArity ``Optic.Iso 2 then
      let cand ← mkAppM ``Optic.Iso.to #[o, x]
      if ← isDefEq cur cand then return cand
  if cur.isAppOfArity ``Optic.Lens.view 4 then
    return ← mkAppM ``Optic.Lens.get #[cur.getArg! 2, cur.getArg! 3]
  return cur

/-- Definitional equality for graph nodes without unfolding local `let` variables. -/
private def nodeDefEq (a b : Expr) : MetaM Bool := do
  if a == b then return true
  withConfig (fun cfg => { cfg with zeta := false, zetaDelta := false }) do
    withReducible (isDefEq a b)

/-- Unfold pipe/setter notation wrappers (`pipe`, `setOf`, `overOf`) and `letE` without
unfolding `Lens.set`, `Lens.over`, structure constructors, or local `let` fvars (unless
`unfoldLetFVar := true`). -/
private partial def whnfStateExpr (e : Expr) (unfoldLetFVar : Bool := false)
    (stopAt? : Option Expr := none) : MetaM Expr := do
  let e := (← instantiateMVars e).consumeMData.headBeta
  if let some stop := stopAt? then
    if ← nodeDefEq e stop then
      return e
  if let .letE _ _ val b _ := e then
    return ← whnfStateExpr (b.instantiate1 val) unfoldLetFVar stopAt?
  if unfoldLetFVar && e.isFVar then
    if let some val ← e.fvarId!.getValue? then
      return ← whnfStateExpr val unfoldLetFVar stopAt?
  if let some c := e.getAppFn.constName? then
    if c == ``Optic.Lens.set || c == ``Optic.Lens.over then
      return e
    if c == ``Optic.Notation.pipe || c == ``Optic.Notation.setOf ||
       c == ``Optic.Notation.overOf then
      if let some e' ← unfoldDefinition? e then
        if e' != e then
          return ← whnfStateExpr e' unfoldLetFVar stopAt?
  return e

/-- Transport `prf : Rel a target` along `hEq : b = a` on the left, producing `Rel b target`. -/
private def transportLeft (rel : Expr) (target : Expr) (hEq : Expr) (prf : Expr) : MetaM Expr := do
  let sTy ← inferType target
  let motive ← withLocalDeclD `z sTy fun z => do
    mkLambdaFVars #[z] (mkApp2 rel z target)
  let eqProp ← mkCongrArg motive hEq
  mkEqMPR eqProp prf

/-- Transport `prf : Rel start a` along `hEq : a = b` on the right, producing `Rel start b`. -/
private def transportRight (rel : Expr) (start : Expr) (hEq : Expr) (prf : Expr) : MetaM Expr := do
  let sTy ← inferType start
  let motive ← withLocalDeclD `z sTy fun z => do
    mkLambdaFVars #[z] (mkApp2 rel start z)
  let eqProp ← mkCongrArg motive hEq
  mkEqMP eqProp prf

/-- Build `ReflTransGen (Modifies L) dst src` from `hEq : dst = src` without requiring
`FactorsLawful L`. -/
private def rtOfEq (modRel : Expr) (src : Expr) (hEq : Expr) : MetaM Expr := do
  let rtRel ← mkAppM ``Optic.ReflTransGen #[modRel]
  let base ← mkAppOptM ``Optic.ReflTransGen.refl #[none, some modRel, some src]
  transportLeft rtRel src hEq base

/-- Unwrap nested `And` conjunctions in a propositional hypothesis up to `depth`. -/
private partial def collectConjuncts (prf : Expr) (depth : Nat := 4) :
    MetaM (Array (Expr × Expr)) := do
  let ty := (← instantiateMVars (← inferType prf)).consumeMData
  if depth > 0 && ty.isAppOfArity ``And 2 then
    let p₁ ← mkAppM ``And.left #[prf]
    let p₂ ← mkAppM ``And.right #[prf]
    return (← collectConjuncts p₁ (depth - 1)) ++ (← collectConjuncts p₂ (depth - 1))
  return #[(ty, prf)]

/-! ### 2. Frame-Algebra Refinement Prover (Zero `Disjoint` Under `ReflTransGen`) -/

/-- Prove `∀ (x y : S), Modifies src x y → Modifies tgt x y` for an atomic (non-`prod`) `src`,
supporting direct match, `Lens.id`, prefix coarsening (`Modifies.coarsen`), product injection
(`Modifies.prod_left`/`prod_right` via `FactorsLawful`), `comp_prod_iff`, and `compIso_iff`. -/
private partial def proveAtomicModifiesRefines? (src tgt : Expr) (fuel : Nat := 24) :
    MetaM (Option Expr) := do
  if fuel == 0 then return none
  let src ← instantiateMVars src
  let tgt ← instantiateMVars tgt
  let nSrc ← whnfOptic src
  let nTgt ← whnfOptic tgt
  let srcTy ← whnf (← inferType nSrc)
  unless srcTy.isAppOfArity ``Optic.Lens 2 do return none
  let sTy := srcTy.getArg! 0
  let tgtTy ← whnf (← inferType nTgt)
  unless tgtTy.isAppOfArity ``Optic.Lens 2 do return none
  unless ← isDefEq (tgtTy.getArg! 0) sTy do return none

  let mkExpected := do
    withLocalDeclD `x sTy fun x =>
    withLocalDeclD `y sTy fun y => do
      let hTy ← mkAppM ``Optic.Modifies #[src, x, y]
      let rTy ← mkAppM ``Optic.Modifies #[tgt, x, y]
      withLocalDeclD `h hTy fun h => do
        mkForallFVars #[x, y, h] rTy

  -- 1. Direct reducible match
  if ← withReducible (isDefEq nSrc nTgt) then
    let fn ← withLocalDeclD `x sTy fun x =>
      withLocalDeclD `y sTy fun y => do
        let hTy ← mkAppM ``Optic.Modifies #[src, x, y]
        withLocalDeclD `h hTy fun h =>
          mkLambdaFVars #[x, y, h] h
    return some (← mkExpectedTypeHint fn (← mkExpected))

  -- 2. Target is `Lens.id`: any modification is trivially `⟨x, rfl⟩`
  if nTgt.isAppOfArity ``Optic.Lens.id 1 then
    let fn ← withLocalDeclD `x sTy fun x =>
      withLocalDeclD `y sTy fun y => do
        let hTy ← mkAppM ``Optic.Modifies #[src, x, y]
        withLocalDeclD `h hTy fun h => do
          let modPred ← withLocalDeclD `v sTy fun v => do
            mkLambdaFVars #[v] (← mkEq x (← mkAppM ``Optic.Lens.set #[tgt, y, v]))
          let body ← mkAppOptM ``Exists.intro
            #[some sTy, some modPred, some x, some (← mkEqRefl x)]
          let rTy ← mkAppM ``Optic.Modifies #[tgt, x, y]
          mkLambdaFVars #[x, y, h] (← mkExpectedTypeHint body rTy)
    return some fn

  -- 3. Prefix coarsening (`src = tgt ∘ₗ inner`) via `Modifies.coarsen`
  let chainSrc ← splitCompChain nSrc
  let chainTgt ← splitCompChain nTgt
  if chainTgt.size > 0 && chainTgt.size <= chainSrc.size then
    let mut prefixOk := true
    for i in [0:chainTgt.size] do
      unless ← withReducible (isDefEq chainSrc[i]! chainTgt[i]!) do
        prefixOk := false
        break
    if prefixOk then
      if chainTgt.size == chainSrc.size then
        let fn ← withLocalDeclD `x sTy fun x =>
          withLocalDeclD `y sTy fun y => do
            let hTy ← mkAppM ``Optic.Modifies #[src, x, y]
            withLocalDeclD `h hTy fun h =>
              mkLambdaFVars #[x, y, h] h
        return some (← mkExpectedTypeHint fn (← mkExpected))
      else
        let outer ← mkCompChain chainTgt
        let inner ← mkCompChain (chainSrc.extract chainTgt.size chainSrc.size)
        let fn ← withLocalDeclD `x sTy fun x =>
          withLocalDeclD `y sTy fun y => do
            let hTy ← mkAppM ``Optic.Modifies #[src, x, y]
            withLocalDeclD `h hTy fun h => do
              let body ← mkAppOptM ``Optic.Modifies.coarsen
                #[none, none, none, some outer, some inner, some x, some y, some h]
              mkLambdaFVars #[x, y, h] body
        return some (← mkExpectedTypeHint fn (← mkExpected))

  -- 4. Target is a product `t₁ ×ₗ t₂`: inject left or right using `FactorsLawful`
  if nTgt.isAppOfArity ``Optic.Lens.prod 5 then
    let t₁ := nTgt.getArg! 3
    let t₂ := nTgt.getArg! 4
    if let some f₁ ← proveAtomicModifiesRefines? nSrc t₁ (fuel - 1) then
      if let some fl₂ ← synthFactorsLawful? t₂ then
        let fn ← withLocalDeclD `x sTy fun x =>
          withLocalDeclD `y sTy fun y => do
            let hTy ← mkAppM ``Optic.Modifies #[src, x, y]
            withLocalDeclD `h hTy fun h => do
              let h₁ := mkApp3 f₁ x y h
              let body ← mkAppOptM ``Optic.Modifies.prod_left
                #[none, none, none, some t₁, some t₂, some fl₂, some x, some y, some h₁]
              mkLambdaFVars #[x, y, h] body
        return some (← mkExpectedTypeHint fn (← mkExpected))
    if let some f₂ ← proveAtomicModifiesRefines? nSrc t₂ (fuel - 1) then
      if let some fl₁ ← synthFactorsLawful? t₁ then
        let fn ← withLocalDeclD `x sTy fun x =>
          withLocalDeclD `y sTy fun y => do
            let hTy ← mkAppM ``Optic.Modifies #[src, x, y]
            withLocalDeclD `h hTy fun h => do
              let h₂ := mkApp3 f₂ x y h
              let body ← mkAppOptM ``Optic.Modifies.prod_right
                #[none, none, none, some t₁, some t₂, some fl₁, some x, some y, some h₂]
              mkLambdaFVars #[x, y, h] body
        return some (← mkExpectedTypeHint fn (← mkExpected))

  -- 5. Target ends with an inner product: `outer ∘ₗ (t₁ ×ₗ t₂)`
  if chainTgt.size >= 2 then
    let lastTgt ← whnfOptic chainTgt[chainTgt.size - 1]!
    if lastTgt.isAppOfArity ``Optic.Lens.prod 5 then
      let outer ← mkCompChain (chainTgt.extract 0 (chainTgt.size - 1))
      if let some hLawful ← proveLawfulLens? outer then
        let t₁ := lastTgt.getArg! 3
        let t₂ := lastTgt.getArg! 4
        let c₁ ← mkAppM ``Optic.Lens.comp #[outer, t₁]
        let c₂ ← mkAppM ``Optic.Lens.comp #[outer, t₂]
        let tgtDist ← mkAppM ``Optic.Lens.prod #[c₁, c₂]
        if let some fDist ← proveAtomicModifiesRefines? nSrc tgtDist (fuel - 1) then
          let fn ← withLocalDeclD `x sTy fun x =>
            withLocalDeclD `y sTy fun y => do
              let hTy ← mkAppM ``Optic.Modifies #[src, x, y]
              withLocalDeclD `h hTy fun h => do
                let hDist := mkApp3 fDist x y h
                let iff ← mkAppOptM ``Optic.Modifies.comp_prod_iff
                  #[none, none, none, none, some outer, some hLawful, some t₁, some t₂,
                    some x, some y]
                let body ← mkAppM ``Iff.mpr #[iff, hDist]
                mkLambdaFVars #[x, y, h] body
          return some (← mkExpectedTypeHint fn (← mkExpected))
    -- 6. Target ends with `Iso.toLens i` (lawful iso)
    if lastTgt.isAppOfArity ``Optic.Iso.toLens 3 then
      let isoExpr := lastTgt.getArg! 2
      if let some hIso ← synthLawfulIso? isoExpr then
        let outer ← mkCompChain (chainTgt.extract 0 (chainTgt.size - 1))
        if let some fOuter ← proveAtomicModifiesRefines? nSrc outer (fuel - 1) then
          let fn ← withLocalDeclD `x sTy fun x =>
            withLocalDeclD `y sTy fun y => do
              let hTy ← mkAppM ``Optic.Modifies #[src, x, y]
              withLocalDeclD `h hTy fun h => do
                let hOut := mkApp3 fOuter x y h
                let iff ← mkAppOptM ``Optic.Modifies.compIso_iff
                  #[none, none, none, some outer, some isoExpr, some hIso, some x, some y]
                let body ← mkAppM ``Iff.mpr #[iff, hOut]
                mkLambdaFVars #[x, y, h] body
          return some (← mkExpectedTypeHint fn (← mkExpected))

  return none

/-- Prove `∀ (x y : S), Modifies src x y → ReflTransGen (Modifies tgt) x y`, supporting
arbitrary permutation, weakening, deduplication, `Lens.unit`, hierarchical coarsening, and
`outer ∘ₗ (a ×ₗ b)` distribution — with ZERO `Disjoint` obligations. -/
partial def proveModifiesRefinesRt? (src tgt : Expr) (fuel : Nat := 24) :
    MetaM (Option Expr) := do
  if fuel == 0 then return none
  let src ← instantiateMVars src
  let tgt ← instantiateMVars tgt
  let nSrc ← whnfOptic src
  let nTgt ← whnfOptic tgt
  let srcTy ← whnf (← inferType nSrc)
  unless srcTy.isAppOfArity ``Optic.Lens 2 do return none
  let sTy := srcTy.getArg! 0
  let tgtTy ← whnf (← inferType nTgt)
  unless tgtTy.isAppOfArity ``Optic.Lens 2 do return none
  unless ← isDefEq (tgtTy.getArg! 0) sTy do return none
  let tgtModRel ← mkAppM ``Optic.Modifies #[tgt]

  let mkExpected := do
    withLocalDeclD `x sTy fun x =>
    withLocalDeclD `y sTy fun y => do
      let hTy ← mkAppM ``Optic.Modifies #[src, x, y]
      let rTy ← mkAppM ``Optic.ReflTransGen #[tgtModRel, x, y]
      withLocalDeclD `h hTy fun h => do
        mkForallFVars #[x, y, h] rTy

  -- 1. Empty source (`Lens.unit`): `x = y`, so `ReflTransGen.refl` transported along `x = y`
  if nSrc.isAppOfArity ``Optic.Lens.unit 1 then
    let .const _ unitLvls := nSrc.getAppFn | return none
    let fn ← withLocalDeclD `x sTy fun x =>
      withLocalDeclD `y sTy fun y => do
        let hTy ← mkAppM ``Optic.Modifies #[src, x, y]
        withLocalDeclD `h hTy fun h => do
          let iff := mkApp3 (mkConst ``Optic.Modifies.unit_iff unitLvls) sTy x y
          let hEq ← mkAppM ``Iff.mp #[iff, h]
          let body ← rtOfEq tgtModRel y hEq
          mkLambdaFVars #[x, y, h] body
    return some (← mkExpectedTypeHint fn (← mkExpected))

  -- 2. Try single-step atomic refinement first (also handles `src = tgt` directly, or
  -- `outer ∘ₗ (a ×ₗ b)` coarsened into `outer`)
  if let some fAtom ← proveAtomicModifiesRefines? nSrc nTgt (fuel - 1) then
    let fn ← withLocalDeclD `x sTy fun x =>
      withLocalDeclD `y sTy fun y => do
        let hTy ← mkAppM ``Optic.Modifies #[src, x, y]
        withLocalDeclD `h hTy fun h => do
          let body ← mkAppM ``Optic.ReflTransGen.single #[mkApp3 fAtom x y h]
          mkLambdaFVars #[x, y, h] body
    return some (← mkExpectedTypeHint fn (← mkExpected))

  -- 3. Product on the left (`l₁ ×ₗ l₂`): split via `Modifies.prod_iff_exists` and chain `trans`
  if nSrc.isAppOfArity ``Optic.Lens.prod 5 then
    let l₁ := nSrc.getArg! 3
    let l₂ := nSrc.getArg! 4
    if let some f₁ ← proveModifiesRefinesRt? l₁ nTgt (fuel - 1) then
      if let some f₂ ← proveModifiesRefinesRt? l₂ nTgt (fuel - 1) then
        let fn ← withLocalDeclD `x sTy fun x =>
          withLocalDeclD `y sTy fun y => do
            let hTy ← mkAppM ``Optic.Modifies #[src, x, y]
            withLocalDeclD `h hTy fun h => do
              let iff ← mkAppOptM ``Optic.Modifies.prod_iff_exists
                #[none, none, none, some l₁, some l₂, some x, some y]
              let ex ← mkAppM ``Iff.mp #[iff, h]
              let cont ← withLocalDeclD `mid sTy fun mid => do
                let conjTy ← mkAppM ``And
                  #[← mkAppM ``Optic.Modifies #[l₁, mid, y],
                    ← mkAppM ``Optic.Modifies #[l₂, x, mid]]
                withLocalDeclD `hm conjTy fun hm => do
                  let hm₁ ← mkAppM ``And.left #[hm]
                  let hm₂ ← mkAppM ``And.right #[hm]
                  let p₂ := mkApp3 f₂ x mid hm₂
                  let p₁ := mkApp3 f₁ mid y hm₁
                  let body ← mkAppM ``Optic.ReflTransGen.trans #[p₂, p₁]
                  mkLambdaFVars #[mid, hm] body
              let body ← mkAppM ``Exists.elim #[ex, cont]
              mkLambdaFVars #[x, y, h] body
        return some (← mkExpectedTypeHint fn (← mkExpected))

  -- 4. Composition ending in `prod` or `unit` on the left (`outer ∘ₗ (a ×ₗ b)` / `outer ∘ₗ unit`)
  let chainSrc ← splitCompChain nSrc
  if chainSrc.size >= 2 then
    let last ← whnfOptic chainSrc[chainSrc.size - 1]!
    let outer ← mkCompChain (chainSrc.extract 0 (chainSrc.size - 1))
    if last.isAppOfArity ``Optic.Lens.prod 5 then
      if let some hLawful ← proveLawfulLens? outer then
        let a := last.getArg! 3
        let b := last.getArg! 4
        let c₁ ← mkAppM ``Optic.Lens.comp #[outer, a]
        let c₂ ← mkAppM ``Optic.Lens.comp #[outer, b]
        let srcDist ← mkAppM ``Optic.Lens.prod #[c₁, c₂]
        if let some fDist ← proveModifiesRefinesRt? srcDist nTgt (fuel - 1) then
          let fn ← withLocalDeclD `x sTy fun x =>
            withLocalDeclD `y sTy fun y => do
              let hTy ← mkAppM ``Optic.Modifies #[src, x, y]
              withLocalDeclD `h hTy fun h => do
                let iff ← mkAppOptM ``Optic.Modifies.comp_prod_iff
                  #[none, none, none, none, some outer, some hLawful, some a, some b,
                    some x, some y]
                let h' ← mkAppM ``Iff.mp #[iff, h]
                let body := mkApp3 fDist x y h'
                mkLambdaFVars #[x, y, h] body
          return some (← mkExpectedTypeHint fn (← mkExpected))
    if last.isAppOfArity ``Optic.Lens.unit 1 then
      if let some hLawful ← proveLawfulLens? outer then
        let fn ← withLocalDeclD `x sTy fun x =>
          withLocalDeclD `y sTy fun y => do
            let hTy ← mkAppM ``Optic.Modifies #[src, x, y]
            withLocalDeclD `h hTy fun h => do
              let uTy := (← whnf (← inferType last)).getArg! 1
              let cont ← withLocalDeclD `u uTy fun u => do
                let setExpr ← mkAppM ``Optic.Lens.set #[← mkAppM ``Optic.Lens.comp #[outer, last], y, u]
                withLocalDeclD `heq (← mkEq x setExpr) fun heq => do
                  let hsg ← mkAppOptM ``Optic.Lens.set_get
                    #[none, none, some outer, some hLawful, some y]
                  let hEqXY ← mkEqTrans heq hsg
                  let body ← rtOfEq tgtModRel y hEqXY
                  mkLambdaFVars #[u, heq] body
              let body ← mkAppM ``Exists.elim #[h, cont]
              mkLambdaFVars #[x, y, h] body
        return some (← mkExpectedTypeHint fn (← mkExpected))

  return none

/-- Convert `hRt : ReflTransGen (Modifies src) dst srcNode` into
`ReflTransGen (Modifies tgt) dst srcNode`. -/
private def refineRtModifies? (src tgt hRt : Expr) : MetaM (Option Expr) := do
  let nSrc ← whnfOptic src
  let nTgt ← whnfOptic tgt
  if ← withReducible (isDefEq nSrc nTgt) then
    return some hRt
  if let some fAtom ← proveAtomicModifiesRefines? nSrc nTgt then
    return some (← mkAppM ``Optic.ReflTransGen.mono #[fAtom, hRt])
  if let some fRt ← proveModifiesRefinesRt? nSrc nTgt then
    return some (← mkAppM ``Optic.ReflTransGen.mono_rt #[fRt, hRt])
  return none

/-- Convert `hMod : Modifies src dst srcNode` into `ReflTransGen (Modifies tgt) dst srcNode`. -/
private def refineModifiesToRt? (src tgt dst srcNode hMod : Expr) : MetaM (Option Expr) := do
  let nSrc ← whnfOptic src
  let nTgt ← whnfOptic tgt
  if ← withReducible (isDefEq nSrc nTgt) then
    return some (← mkAppM ``Optic.ReflTransGen.single #[hMod])
  if let some fAtom ← proveAtomicModifiesRefines? nSrc nTgt then
    return some (← mkAppM ``Optic.ReflTransGen.single #[mkApp3 fAtom dst srcNode hMod])
  if let some fRt ← proveModifiesRefinesRt? nSrc nTgt then
    return some (mkApp3 fRt dst srcNode hMod)
  return none

/-- Lift `hRt : ReflTransGen (Modifies inner) a' (outer.get x)` through `outer` and flatten any
inner product `outer ∘ₗ (i₁ ×ₗ … ×ₗ iₖ)` into `(outer ∘ₗ i₁) ×ₗ … ×ₗ (outer ∘ₗ iₖ)`.
Returns `(liftedLens, liftedPrf)`. -/
private def rtLiftFlatten? (outer inner hRt : Expr) : MetaM (Option (Expr × Expr)) := do
  let some hLawful ← proveLawfulLens? outer | return none
  let nInner ← whnfOptic inner
  let outerTy ← whnf (← inferType outer)
  unless outerTy.isAppOfArity ``Optic.Lens 2 do return none
  let sTy := outerTy.getArg! 0
  if nInner.isAppOfArity ``Optic.Lens.unit 1 then
    let lifted ← mkAppOptM ``Optic.Modifies.rt_lift_unit
      #[none, none, some outer, some hLawful, none, none, some hRt]
    let uLens ← mkUnitLens sTy
    -- Match universe of `rt_lift_unit`'s output lens
    let liftedTy ← inferType lifted
    match matchRtModifies? liftedTy with
    | some (_, actualUnit, _, _) => return some (actualUnit, lifted)
    | none => return some (uLens, lifted)
  let lifted ← mkAppOptM ``Optic.Modifies.rt_lift
    #[none, none, none, some outer, some hLawful, some inner, none, none, some hRt]
  let compLens ← mkAppM ``Optic.Lens.comp #[outer, inner]
  let leaves ← splitProdTree nInner
  if leaves.isEmpty then
    let uLens ← mkUnitLens sTy
    if let some prf ← refineRtModifies? compLens uLens lifted then
      return some (uLens, prf)
    return some (compLens, lifted)
  if leaves.size == 1 && !nInner.isAppOfArity ``Optic.Lens.prod 5 then
    return some (compLens, lifted)
  let flatLeaves ← leaves.mapM fun leaf => mkAppM ``Optic.Lens.comp #[outer, leaf]
  let flatLens ← mkProdTree flatLeaves
  if let some flatPrf ← refineRtModifies? compLens flatLens lifted then
    return some (flatLens, flatPrf)
  return some (compLens, lifted)

/-- Combine two sequential `ReflTransGen (Modifies _)` steps:
`h₁ : ReflTransGen (Modifies l₁) mid src` followed by `h₂ : ReflTransGen (Modifies l₂) dst mid`
into `(combinedLens, combinedPrf : ReflTransGen (Modifies combinedLens) dst src)`. -/
private def combineRtSteps? (l₁ h₁ l₂ h₂ : Expr) : MetaM (Option (Expr × Expr)) := do
  let n₁ ← whnfOptic l₁
  let n₂ ← whnfOptic l₂
  -- If `l₁` is `Lens.unit`, drop it (`h₁` implies `mid = src`)
  if n₁.isAppOfArity ``Optic.Lens.unit 1 then
    if let some h₁' ← refineRtModifies? l₁ l₂ h₁ then
      let prf ← mkAppM ``Optic.ReflTransGen.trans #[h₂, h₁']
      return some (l₂, prf)
  -- If `l₂` is `Lens.unit`, drop it
  if n₂.isAppOfArity ``Optic.Lens.unit 1 then
    if let some h₂' ← refineRtModifies? l₂ l₁ h₂ then
      let prf ← mkAppM ``Optic.ReflTransGen.trans #[h₂', h₁]
      return some (l₁, prf)
  -- If `l₂` refines `l₁`, avoid expanding the product
  if let some h₂' ← refineRtModifies? l₂ l₁ h₂ then
    let prf ← mkAppM ``Optic.ReflTransGen.trans #[h₂', h₁]
    return some (l₁, prf)
  -- If `l₁` refines `l₂`, avoid expanding the product
  if let some h₁' ← refineRtModifies? l₁ l₂ h₁ then
    let prf ← mkAppM ``Optic.ReflTransGen.trans #[h₂, h₁']
    return some (l₂, prf)
  -- General case: combine via `Modifies.rt_prod_comp`
  if let some fl₁ ← synthFactorsLawful? l₁ then
    if let some fl₂ ← synthFactorsLawful? l₂ then
      let prodL ← mkAppM ``Optic.Lens.prod #[l₁, l₂]
      let prf ← mkAppOptM ``Optic.Modifies.rt_prod_comp
        #[none, none, none, some l₁, some l₂, some fl₁, some fl₂, none, none, none,
          some h₁, some h₂]
      return some (prodL, prf)
  return none

/-! ### 3. Substate Frame Index (for Arbitrary-Depth Lifting) -/

/-- A local-context frame or equality edge on any state/substate type `stateTy`. -/
private structure SubstateFrame where
  stateTy : Expr
  isRt : Bool
  w? : Option Expr  -- `none` for `Eq`, `some W` for `Modifies W` / `ReflTransGen (Modifies W)`
  dst : Expr
  src : Expr
  prf : Expr
  deriving Inhabited

/-- Harvest all `Eq`, `Modifies`, and `ReflTransGen (Modifies _)` hypotheses across all types
in the local context (including symmetric directions when lawful/`FactorsLawful`). -/
private def collectSubstateFrames : MetaM (Array SubstateFrame) := do
  let mut out : Array SubstateFrame := #[]
  for decl in (← getLCtx) do
    if decl.isImplementationDetail then continue
    if decl.isLet then continue
    let conjuncts ← collectConjuncts decl.toExpr
    for (dt, prf) in conjuncts do
      if let some (sTy, w, dst, src) := matchRtModifies? dt then
        out := out.push { stateTy := sTy, isRt := true, w? := some w, dst, src, prf }
        if let some fl ← synthFactorsLawful? w then
          let sym ← mkAppOptM ``Optic.Modifies.rt_symm
            #[none, none, some w, some fl, some dst, some src, some prf]
          out := out.push { stateTy := sTy, isRt := true, w? := some w, dst := src, src := dst, prf := sym }
      else if let some (sTy, w, dst, src) := matchModifies? dt then
        out := out.push { stateTy := sTy, isRt := false, w? := some w, dst, src, prf }
        if let some fl ← synthFactorsLawful? w then
          let single ← mkAppM ``Optic.Modifies.rt_single #[prf]
          let sym ← mkAppOptM ``Optic.Modifies.rt_symm
            #[none, none, some w, some fl, some dst, some src, some single]
          out := out.push { stateTy := sTy, isRt := true, w? := some w, dst := src, src := dst, prf := sym }
      else if let some (ty, a, b) := dt.eq? then
        if !(← isProp ty) then
          out := out.push { stateTy := ty, isRt := true, w? := none, dst := a, src := b, prf }
          let sym ← mkEqSymm prf
          out := out.push { stateTy := ty, isRt := true, w? := none, dst := b, src := a, prf := sym }
  return out

/-- Search `subFrames` (via small BFS on type `subTy`) for a frame connecting `dst` to `src`
whose write-set, lifted through `prefixLens`, refines `tgtL?` (if provided).
Returns `(usedSubLens, prf : ReflTransGen (Modifies usedSubLens) dst src)`. -/
private def findSubstateFrame? (subFrames : Array SubstateFrame) (subTy dst src : Expr)
    (prefixLens : Array Expr) (tgtL? : Option Expr) : MetaM (Option (Expr × Expr)) := do
  -- Filter frames matching `subTy`
  let mut relFrames : Array SubstateFrame := #[]
  for f in subFrames do
    if ← isDefEq f.stateTy subTy then
      -- Check if lifted write-set is acceptable under `tgtL?`
      let ok ← match f.w?, tgtL? with
        | none, _ => pure true
        | some _, none => pure true
        | some w, some tgtL =>
          let fullW ← if prefixLens.isEmpty then pure w
            else mkCompChain (prefixLens.push w)
          pure (← proveModifiesRefinesRt? fullW tgtL).isSome
      if ok then
        relFrames := relFrames.push f
  if relFrames.isEmpty then return none

  -- Build tiny node table & BFS from `dst` to `src`
  let dstNorm ← normalizeOpticView dst
  let srcNorm ← normalizeOpticView src
  let mut nodes : Array Expr := #[dstNorm, srcNorm]
  let findOrAdd (nodes : Array Expr) (e : Expr) : MetaM (Array Expr × Nat) := do
    let e ← normalizeOpticView e
    for i in [0:nodes.size] do
      if ← withReducible (isDefEq nodes[i]! e) then
        return (nodes, i)
    return (nodes.push e, nodes.size)

  let mut adj : Array (Array (Nat × SubstateFrame)) := #[#[], #[]]
  for f in relFrames do
    let (nodes', u) ← findOrAdd nodes f.dst
    nodes := nodes'
    while adj.size < nodes.size do adj := adj.push #[]
    let (nodes'', v) ← findOrAdd nodes f.src
    nodes := nodes''
    while adj.size < nodes.size do adj := adj.push #[]
    adj := adj.modify u (·.push (v, f))

  -- BFS from 0 (`dst`) to 1 (`src`)
  let mut visited : Array Bool := Array.replicate nodes.size false
  let mut parent : Array (Option (Nat × SubstateFrame)) := Array.replicate nodes.size none
  visited := visited.set! 0 true
  let mut queue : Array Nat := #[0]
  let mut qHead : Nat := 0
  let mut found := false
  while qHead < queue.size && !found do
    let u := queue[qHead]!
    qHead := qHead + 1
    for (v, f) in adj[u]! do
      if !visited[v]! then
        visited := visited.set! v true
        parent := parent.set! v (some (u, f))
        if v == 1 then
          found := true
          break
        queue := queue.push v

  unless found do return none

  -- Reconstruct path edges `0 → ... → 1`
  let mut revEdges : Array SubstateFrame := #[]
  let mut cur := 1
  while cur != 0 do
    let some (p, f) := parent[cur]! | return none
    revEdges := revEdges.push f
    cur := p
  let pathEdges := revEdges.reverse

  -- Fold path edges from right to left (from `src` backwards to `dst`)
  let uLens ← mkUnitLens subTy
  let mut curLens : Expr := uLens
  let mut curPrf? : Option Expr := none
  let mut curTarget : Expr := src
  for i in [0:pathEdges.size] do
    let f := pathEdges[pathEdges.size - 1 - i]!
    match f.w? with
    | none =>
      -- `f.prf : f.dst = f.src`
      match curPrf? with
      | none =>
        let modRel ← mkAppM ``Optic.Modifies #[uLens]
        curPrf? := some (← rtOfEq modRel f.src f.prf)
        curTarget := f.src
      | some acc =>
        let modRel ← mkAppM ``Optic.Modifies #[curLens]
        let rtRel ← mkAppM ``Optic.ReflTransGen #[modRel]
        curPrf? := some (← transportLeft rtRel curTarget f.prf acc)
    | some w =>
      let stepRt ← if f.isRt then pure f.prf
        else mkAppM ``Optic.ReflTransGen.single #[f.prf]
      match curPrf? with
      | none =>
        curLens := w
        curPrf? := some stepRt
        curTarget := f.src
      | some acc =>
        -- `acc : ReflTransGen (Modifies curLens) f.src curTarget`
        -- `stepRt : ReflTransGen (Modifies w) f.dst f.src`
        let some (newL, newP) ← combineRtSteps? curLens acc w stepRt | return none
        curLens := newL
        curPrf? := some newP

  let some finalPrf := curPrf? | return none
  let modRel ← mkAppM ``Optic.Modifies #[curLens]
  let expected ← mkAppM ``Optic.ReflTransGen #[modRel, dst, src]
  return some (curLens, ← mkExpectedTypeHint finalPrf expected)

/-! ### 4. Engine A — Symbolic State-Update Diff -/

/-- A changed field path uncovered by the target write-set, paired with its focused
equality subgoal `p.get s' = p.get s`. -/
private structure MissingWrite where
  path : Expr
  mvarId : MVarId
  deriving Inhabited

/-- Output of concrete diffing `e'` against `e`. -/
private inductive DiffResult where
  | unchanged
  | diffed (usedLens : Expr) (prf : Expr) (decomposed : Bool) (missing : Array MissingWrite)

/-- Build a witness tuple for `L` filling modified slots from `s'` and untouched slots from `s`. -/
private partial def buildWitnessTuple (L s' s : Expr) : MetaM Expr := do
  let nL ← whnfOptic L
  if nL.isAppOfArity ``Optic.Lens.unit 1 then
    let lTy ← whnf (← inferType nL)
    let unitTy := lTy.getArg! 1
    let .const _ lvls := unitTy.getAppFn | return ← mkAppM ``PUnit.unit #[]
    return mkConst ``PUnit.unit lvls
  if nL.isAppOfArity ``Optic.Lens.prod 5 then
    let l₁ := nL.getArg! 3
    let l₂ := nL.getArg! 4
    let w₁ ← buildWitnessTuple l₁ s' s
    let w₂ ← buildWitnessTuple l₂ s' s
    return ← mkAppM ``Prod.mk #[w₁, w₂]
  let v' ← mkAppM ``Optic.Lens.get #[L, s']
  let v ← mkAppM ``Optic.Lens.get #[L, s]
  if ← withReducible (isDefEq v' v) then
    return v
  return v'

/-- Fast path for Engine A: try closing `ReflTransGen (Modifies L) s' s` or `Modifies L s' s`
in 1 step via `⟨witnessTuple, rfl⟩` (or `ReflTransGen.single ⟨witnessTuple, rfl⟩`). -/
private def tryOneStepWitness? (L s' s : Expr) (isRt : Bool) : MetaM (Option Expr) := do
  let nL ← whnfOptic L
  if nL.isAppOfArity ``Optic.Lens.unit 1 then
    if ← withReducible (isDefEq s' s) then
      if isRt then
        let modRel ← mkAppM ``Optic.Modifies #[L]
        let prf ← mkAppOptM ``Optic.ReflTransGen.refl #[none, some modRel, some s]
        let expected ← mkAppM ``Optic.ReflTransGen #[modRel, s', s]
        return some (← mkExpectedTypeHint prf expected)
      else
        let w ← buildWitnessTuple L s' s
        let prf ← mkAppOptM ``Exists.intro #[none, none, some w, some (← mkEqRefl s')]
        let expected ← mkAppM ``Optic.Modifies #[L, s', s]
        return some (← mkExpectedTypeHint prf expected)
    return none

  let prf? ← commitWhenSomeNoEx? do
    let w ← buildWitnessTuple L s' s
    let setExpr ← mkAppM ``Optic.Lens.set #[L, s, w]
    unless ← withReducible (isDefEq s' setExpr) do
      return none
    let lTy ← whnf (← inferType L)
    unless lTy.isAppOfArity ``Optic.Lens 2 do return none
    let aTy := lTy.getArg! 1
    let modPred ← withLocalDeclD `v aTy fun v => do
      mkLambdaFVars #[v] (← mkEq s' (← mkAppM ``Optic.Lens.set #[L, s, v]))
    let hMod ← mkAppOptM ``Exists.intro #[some aTy, some modPred, some w, some (← mkEqRefl s')]
    let modExpected ← mkAppM ``Optic.Modifies #[L, s', s]
    let hMod ← mkExpectedTypeHint hMod modExpected
    if isRt then
      let prf ← mkAppM ``Optic.ReflTransGen.single #[hMod]
      let modRel ← mkAppM ``Optic.Modifies #[L]
      let expected ← mkAppM ``Optic.ReflTransGen #[modRel, s', s]
      return some (← mkExpectedTypeHint prf expected)
    else
      return some hMod
  return prf?

/-- Check whether `e` is an application of a structure constructor (`make_lenses`-registered
or `Prod`), returning `(structTy, fieldLenses, fieldArgs)` if so. -/
private def matchStructCtorApp? (e : Expr) : MetaM (Option (Expr × Array Expr × Array Expr)) := do
  let e := e.consumeMData
  let some ctorName := e.getAppFn.constName? | return none
  let env ← getEnv
  let some (.ctorInfo ctorInfo) := env.find? ctorName | return none
  let structName := ctorInfo.induct
  let args := e.getAppArgs
  unless args.size == ctorInfo.numParams + ctorInfo.numFields do return none
  let structTy ← inferType e
  -- Special case: `Prod.mk`
  if structName == ``Prod && ctorInfo.numFields == 2 then
    let aTy := args[0]!
    let bTy := args[1]!
    let fstL ← mkAppOptM ``Optic.Lens.fst #[some aTy, some bTy]
    let sndL ← mkAppOptM ``Optic.Lens.snd #[some aTy, some bTy]
    return some (structTy, #[fstL, sndL], #[args[2]!, args[3]!])
  -- General `make_lenses`-registered structure
  let some structInfo := getStructureInfo? env structName | return none
  unless structInfo.fieldNames.size == ctorInfo.numFields do return none
  let mut lenses : Array Expr := #[]
  for i in [0:ctorInfo.numFields] do
    let some fl ← mkStructFieldLens? structTy i | return none
    lenses := lenses.push fl
  let fieldArgs := args.extract ctorInfo.numParams args.size
  return some (structTy, lenses, fieldArgs)

/-- Check if type `ty` is `Prod` or a `make_lenses`-registered structure. -/
private def isRegisteredLensStructType (ty : Expr) : MetaM Bool := do
  let ty ← whnf (← instantiateMVars ty)
  let some structName := ty.getAppFn.constName? | return false
  if structName == ``Prod then return true
  let env ← getEnv
  let some structInfo := getStructureInfo? env structName | return false
  if structInfo.fieldNames.isEmpty then return false
  return (Optic.Derive.lookupStructFieldLens? env structName 0).isSome

/-- Create a focused equality metavariable for an uncovered leaf field `(curPrefix ++ seg)`
with value `v'` vs `v`. Prefers typing the subgoal as `fullPath.get rootS' = fullPath.get rootS`
when reducibly defeq to `v' = v`. -/
private def mkMissingEqMVar (rootS' rootS fullPath v' v : Expr) : MetaM MVarId := do
  let rawTy ← mkEq v' v
  let pGet' ← mkAppM ``Optic.Lens.get #[fullPath, rootS']
  let pGet ← mkAppM ``Optic.Lens.get #[fullPath, rootS]
  let niceTy ← mkEq pGet' pGet
  let goalTy ←
    if (← withReducible (isDefEq pGet' v')) && (← withReducible (isDefEq pGet v)) then
      pure niceTy
    else
      pure rawTy
  let mvar ← mkFreshExprMVar goalTy
  return mvar.mvarId!

/-- Check if an atomic lens `fullPath` is covered by `tgtL`. -/
private def isLensCoveredByTarget (fullPath tgtL : Expr) : MetaM Bool := do
  return (← proveAtomicModifiesRefines? fullPath tgtL).isSome

/-- Recursively diff `e'` against `e` (both of type `T`) under lens path `curPrefix : Lens S T`.
- When `tgtL? = some tgtL`, stops descending as soon as a changed field path is covered by `tgtL`.
- When `tgtL? = none`, descends as deeply as possible to produce the tightest write-set (for Engine C).
- When `allowMissing = true`, creates focused equality subgoals for uncovered changed leaves. -/
private partial def diffConcrete
    (rootS' rootS : Expr)
    (tgtL? : Option Expr)
    (allowMissing : Bool)
    (subFrames : Array SubstateFrame)
    (curPrefix : Array Expr)
    (e' e : Expr)
    (fuel : Nat := 32) : MetaM (Option DiffResult) := do
  if fuel == 0 then return none
  let e' ← instantiateMVars e'
  let e ← instantiateMVars e

  -- 0. Unchanged fast path
  if ← withReducible (isDefEq e' e) then
    return some .unchanged

  let curTy ← inferType e

  -- 1. Substate frame lookup (for nested fields `curPrefix.size > 0`)
  if !curPrefix.isEmpty && !subFrames.isEmpty then
    if let some (subW, subPrf) ← findSubstateFrame? subFrames curTy e' e curPrefix tgtL? then
      return some (.diffed subW subPrf true #[])

  -- Normalize notation wrappers (`&`, `.~`, `%~`, `letE`, and local `let`s on `e'`)
  let ne' ← whnfStateExpr e' (unfoldLetFVar := true) (stopAt? := some e)
  if ← withReducible (isDefEq ne' e) then
    return some .unchanged

  -- 2. Lens update step: `Lens.set l base v` or `Lens.over l f base`
  let lensStep? : Option (Expr × Expr × Expr × Bool) :=
    if ne'.isAppOfArity ``Optic.Lens.set 5 then
      some (ne'.getArg! 2, ne'.getArg! 3, ne'.getArg! 4, false)
    else if ne'.isAppOfArity ``Optic.Lens.over 5 then
      some (ne'.getArg! 2, ne'.getArg! 4, ne'.getArg! 3, true)
    else
      none

  if let some (l, base, valOrFn, isOver) := lensStep? then
    let lSegs ← splitCompChain l
    let fullPath ← if curPrefix.isEmpty then pure l else mkCompChain (curPrefix ++ lSegs)
    let covered ← match tgtL? with
      | none => pure true
      | some tgtL => isLensCoveredByTarget fullPath tgtL

    -- Try peeling this lens step directly when covered
    if covered then
      -- Only peel if `base` can reach `e`!
      if let some baseRes ← diffConcrete rootS' rootS tgtL? allowMissing subFrames curPrefix base e (fuel - 1) then
        let stepPrf ← if isOver then
            mkAppM ``Optic.Modifies.rt_over #[l, valOrFn, base]
          else
            mkAppM ``Optic.Modifies.rt_set #[l, base, valOrFn]
        let modRel ← mkAppM ``Optic.Modifies #[l]
        let stepExpected ← mkAppM ``Optic.ReflTransGen #[modRel, e', base]
        let stepPrf ← mkExpectedTypeHint stepPrf stepExpected
        match baseRes with
        | .unchanged =>
          let expected ← mkAppM ``Optic.ReflTransGen #[modRel, e', e]
          return some (.diffed l (← mkExpectedTypeHint stepPrf expected) true #[])
        | .diffed baseL basePrf _ baseMissing =>
          if let some (combL, combPrf) ← combineRtSteps? baseL basePrf l stepPrf then
            return some (.diffed combL combPrf true baseMissing)
    else
      -- If BOTH `e'` and `e` reduce to structure constructors (e.g. reordered `{ₗ s₀ with … }`
      -- against `{ₗ s₀ with … }`), prefer structural field-by-field diff in Step 3 so shared
      -- updates cancel cleanly instead of being attributed to `base`.
      let bothStructCtors ← do
        if ← isRegisteredLensStructType curTy then
          let we' ← withReducible (whnf ne')
          let we ← withReducible (whnf e)
          pure ((← matchStructCtorApp? we').isSome && (← matchStructCtorApp? we).isSome)
        else
          pure false

      unless bothStructCtors do
        -- `l` is NOT covered as a whole: try descending into `val` vs `l.get base` (for nested
        -- struct updates or substate lifting inside `l.set base v`)
        if !isOver then
          if let some _ ← proveLawfulLens? l then
            let oldVal ← mkAppM ``Optic.Lens.get #[l, base]
            let innerPrefix := curPrefix ++ lSegs
            if let some valRes ← diffConcrete rootS' rootS tgtL? allowMissing subFrames innerPrefix valOrFn oldVal (fuel - 1) then
              if let some baseRes ← diffConcrete rootS' rootS tgtL? allowMissing subFrames curPrefix base e (fuel - 1) then
                match valRes with
                | .unchanged =>
                  -- `valOrFn` is defeq to `l.get base` -> `l.set base valOrFn = base` via `Lens.set_get`
                  let some hLawful ← proveLawfulLens? l | pure ()
                  let hsg ← mkAppOptM ``Optic.Lens.set_get
                    #[none, none, some l, some hLawful, some base]
                  let hEq ← mkExpectedTypeHint hsg (← mkEq e' base)
                  match baseRes with
                  | .unchanged =>
                    let uLens ← mkUnitLens curTy
                    let modRel ← mkAppM ``Optic.Modifies #[uLens]
                    let prf ← rtOfEq modRel base hEq
                    let expected ← mkAppM ``Optic.ReflTransGen #[modRel, e', e]
                    return some (.diffed uLens (← mkExpectedTypeHint prf expected) true #[])
                  | .diffed baseL basePrf _ baseMissing =>
                    let modRel ← mkAppM ``Optic.Modifies #[baseL]
                    let rtRel ← mkAppM ``Optic.ReflTransGen #[modRel]
                    let prf ← transportLeft rtRel e hEq basePrf
                    return some (.diffed baseL prf true baseMissing)
                | .diffed valL valPrf _ valMissing =>
                  if let some (liftedL, liftedPrf) ← rtLiftFlatten? l valL valPrf then
                    let modRel ← mkAppM ``Optic.Modifies #[liftedL]
                    let liftedPrf ← mkExpectedTypeHint liftedPrf
                      (← mkAppM ``Optic.ReflTransGen #[modRel, e', base])
                    match baseRes with
                    | .unchanged =>
                      let expected ← mkAppM ``Optic.ReflTransGen #[modRel, e', e]
                      return some (.diffed liftedL (← mkExpectedTypeHint liftedPrf expected) true valMissing)
                    | .diffed baseL basePrf _ baseMissing =>
                      if let some (combL, combPrf) ← combineRtSteps? baseL basePrf liftedL liftedPrf then
                        return some (.diffed combL combPrf true (baseMissing ++ valMissing))

        if allowMissing then
          if let some hLawful ← proveLawfulLens? l then
            if let some baseRes ← diffConcrete rootS' rootS tgtL? true subFrames curPrefix base e (fuel - 1) then
              let oldVal ← mkAppM ``Optic.Lens.get #[l, base]
              let newVal ← if isOver then pure (mkApp valOrFn oldVal) else pure valOrFn
              let mId ← mkMissingEqMVar rootS' rootS fullPath newVal oldVal
              let setFn ← mkAppM ``Optic.Lens.set #[l, base]
              let h1 ← mkCongrArg setFn (mkMVar mId)
              let h2 ← mkAppOptM ``Optic.Lens.set_get
                #[none, none, some l, some hLawful, some base]
              let hEqStep ← mkEqTrans h1 h2
              let hEqStep ← mkExpectedTypeHint hEqStep (← mkEq e' base)
              let mw : MissingWrite := { path := fullPath, mvarId := mId }
              match baseRes with
              | .unchanged =>
                let uLens ← mkUnitLens curTy
                let modRel ← mkAppM ``Optic.Modifies #[uLens]
                let prf ← rtOfEq modRel base hEqStep
                let expected ← mkAppM ``Optic.ReflTransGen #[modRel, e', e]
                return some (.diffed uLens (← mkExpectedTypeHint prf expected) true #[mw])
              | .diffed baseL basePrf _ baseMissing =>
                let modRel ← mkAppM ``Optic.Modifies #[baseL]
                let rtRel ← mkAppM ``Optic.ReflTransGen #[modRel]
                let prf ← transportLeft rtRel e hEqStep basePrf
                return some (.diffed baseL prf true (baseMissing.push mw))
        return none

  -- 3. Structure constructor diff (`S.mk ...` or `Prod.mk ...`)
  let ctorInfo? ← do
    if let some info ← matchStructCtorApp? ne' then
      pure (some info)
    else if ← isRegisteredLensStructType curTy then
      let we' ← withReducible (whnf ne')
      matchStructCtorApp? we'
    else
      pure none

  let some (_, fieldLenses, fieldArgs') := ctorInfo? | return none

  -- Extract old field values from `e` (if `e` is also a constructor, extract directly;
  -- otherwise project via `fieldLenses[i].get e`)
  let oldFieldArgs? ← do
    let ne ← whnfStateExpr e (unfoldLetFVar := false)
    if let some (_, _, args) ← matchStructCtorApp? ne then
      pure (some args)
    else if ← isRegisteredLensStructType curTy then
      let we ← withReducible (whnf ne)
      if let some (_, _, args) ← matchStructCtorApp? we then
        pure (some args)
      else
        pure none
    else
      pure none

  let mut curState : Expr := e
  let mut curLens? : Option Expr := none
  let mut curPrf? : Option Expr := none
  let mut missing : Array MissingWrite := #[]
  let mut anyChanged := false

  for i in [0:fieldLenses.size] do
    let fl := fieldLenses[i]!
    let f' := fieldArgs'[i]!
    let fOld ← match oldFieldArgs? with
      | some args => pure args[i]!
      | none => mkAppM ``Optic.Lens.get #[fl, e]
    if ← withReducible (isDefEq f' fOld) then
      continue
    anyChanged := true
    let nextState ← mkAppM ``Optic.Lens.set #[fl, curState, f']
    let fullPath ← mkCompChain (curPrefix.push fl)
    let coveredDirectly ← match tgtL? with
      | none => pure false  -- In minimal-diff mode, always try descending deeper first!
      | some tgtL => isLensCoveredByTarget fullPath tgtL

    if coveredDirectly then
      -- O(1): do NOT unfold inner structure of `f'`
      let stepPrf ← mkAppM ``Optic.Modifies.rt_set #[fl, curState, f']
      match curLens?, curPrf? with
      | none, none =>
        curLens? := some fl
        curPrf? := some stepPrf
      | some cL, some cP =>
        let some (combL, combP) ← combineRtSteps? cL cP fl stepPrf | return none
        curLens? := some combL
        curPrf? := some combP
      | _, _ => return none
      curState := nextState
    else
      -- Try descending recursively into `(f', fOld)`
      let innerOld ← mkAppM ``Optic.Lens.get #[fl, curState]
      let innerRes? ← diffConcrete rootS' rootS tgtL? allowMissing subFrames
        (curPrefix.push fl) f' innerOld (fuel - 1)
      match innerRes? with
      | some .unchanged =>
        -- `f'` turned out defeq to `fl.get curState`
        curState := nextState
      | some (.diffed innerL innerPrf _ innerMissing) =>
        let some (liftedL, liftedPrf) ← rtLiftFlatten? fl innerL innerPrf | return none
        missing := missing ++ innerMissing
        match curLens?, curPrf? with
        | none, none =>
          curLens? := some liftedL
          curPrf? := some liftedPrf
        | some cL, some cP =>
          let some (combL, combP) ← combineRtSteps? cL cP liftedL liftedPrf | return none
          curLens? := some combL
          curPrf? := some combP
        | _, _ => return none
        curState := nextState
      | none =>
        -- Leaf field could not be decomposed further
        match tgtL? with
        | none =>
          -- Minimal-diff mode (Engine C): record this leaf lens `fl`
          let stepPrf ← mkAppM ``Optic.Modifies.rt_set #[fl, curState, f']
          match curLens?, curPrf? with
          | none, none =>
            curLens? := some fl
            curPrf? := some stepPrf
          | some cL, some cP =>
            let some (combL, combP) ← combineRtSteps? cL cP fl stepPrf | return none
            curLens? := some combL
            curPrf? := some combP
          | _, _ => return none
          curState := nextState
        | some _ =>
          if allowMissing then
            let some hLawful ← proveLawfulLens? fl | return none
            let mId ← mkMissingEqMVar rootS' rootS fullPath f' innerOld
            let setFn ← mkAppM ``Optic.Lens.set #[fl, curState]
            let h1 ← mkCongrArg setFn (mkMVar mId)
            let h2 ← mkAppOptM ``Optic.Lens.set_get
              #[none, none, some fl, some hLawful, some curState]
            let hEqStep ← mkEqTrans h1 h2
            missing := missing.push { path := fullPath, mvarId := mId }
            match curLens?, curPrf? with
            | none, none =>
              let uLens ← mkUnitLens curTy
              let modRel ← mkAppM ``Optic.Modifies #[uLens]
              let prf ← rtOfEq modRel curState hEqStep
              curLens? := some uLens
              curPrf? := some prf
            | some cL, some cP =>
              let modRel ← mkAppM ``Optic.Modifies #[cL]
              let rtRel ← mkAppM ``Optic.ReflTransGen #[modRel]
              let prf ← transportLeft rtRel e hEqStep cP
              curPrf? := some prf
            | _, _ => return none
            curState := nextState
          else
            return none

  unless anyChanged do
    return some .unchanged

  -- Verify `curState` is reducibly defeq to `e'`
  unless ← withReducible (isDefEq curState e') do
    return none

  match curLens?, curPrf? with
  | some finalL, some finalP =>
    let modRel ← mkAppM ``Optic.Modifies #[finalL]
    let expected ← mkAppM ``Optic.ReflTransGen #[modRel, e', e]
    return some (.diffed finalL (← mkExpectedTypeHint finalP expected) true missing)
  | _, _ =>
    return some .unchanged

/-- Convert a `ReflTransGen (Modifies L) s' s` proof to `Modifies L s' s` if `LawfulLens L`
can be proved via typeclass synthesis or `Lens.lawful_prod` + `proveDisjoint?`. -/
private def rtToSingleModifies? (L s' s hRt : Expr) : MetaM (Option Expr) := do
  let some hLawful ← proveLawfulLens? L | return none
  let iff ← mkAppOptM ``Optic.Modifies.rt_iff_of_lawful
    #[none, none, some L, some hLawful, some s', some s]
  return some (← mkAppM ``Iff.mp #[iff, hRt])

/-- Engine A complete solver (zero open subgoals):
1. Fast 1-step witness tuple (`⟨w, rfl⟩` / `ReflTransGen.single ⟨w, rfl⟩`),
2. Recursive concrete diff (`diffConcrete`) + refinement into `L`. -/
private def engineASolve? (L s' s : Expr) (isRt : Bool) (subFrames : Array SubstateFrame) :
    MetaM (Option Expr) := do
  -- Fast path: 1-step witness tuple
  if let some prf ← tryOneStepWitness? L s' s isRt then
    return some prf

  -- Recursive concrete diff (no missing writes allowed)
  let some res ← diffConcrete s' s (some L) (allowMissing := false) subFrames #[] s' s
    | return none
  match res with
  | .unchanged =>
    if isRt then
      let modRel ← mkAppM ``Optic.Modifies #[L]
      let prf ← mkAppOptM ``Optic.ReflTransGen.refl #[none, some modRel, some s]
      let expected ← mkAppM ``Optic.ReflTransGen #[modRel, s', s]
      return some (← mkExpectedTypeHint prf expected)
    else
      if let some fl ← synthFactorsLawful? L then
        let prf ← mkAppOptM ``Optic.Modifies.refl_of_factorsLawful
          #[none, none, some L, some fl, some s]
        let expected ← mkAppM ``Optic.Modifies #[L, s', s]
        return some (← mkExpectedTypeHint prf expected)
      return none
  | .diffed usedL prf _ _ =>
    let some hRt ← refineRtModifies? usedL L prf | return none
    let modRel ← mkAppM ``Optic.Modifies #[L]
    let hRt ← mkExpectedTypeHint hRt (← mkAppM ``Optic.ReflTransGen #[modRel, s', s])
    if isRt then
      return some hRt
    else
      rtToSingleModifies? L s' s hRt

/-- Engine A missing-write analyzer: diffs `s'` against `s` allowing missing writes,
returning `(partialProof, missingWrites)` if concrete decomposition made progress. -/
private def engineAMissingWrites? (L s' s : Expr) (isRt : Bool) (subFrames : Array SubstateFrame) :
    MetaM (Option (Expr × Array MissingWrite)) := do
  let some res ← diffConcrete s' s (some L) (allowMissing := true) subFrames #[] s' s
    | return none
  match res with
  | .unchanged => return none
  | .diffed usedL prf decomposed missing =>
    if !decomposed || missing.isEmpty then
      return none
    let some hRt ← refineRtModifies? usedL L prf | return none
    let modRel ← mkAppM ``Optic.Modifies #[L]
    let hRt ← mkExpectedTypeHint hRt (← mkAppM ``Optic.ReflTransGen #[modRel, s', s])
    if isRt then
      return some (hRt, missing)
    else
      if let some hMod ← rtToSingleModifies? L s' s hRt then
        return some (hMod, missing)
      -- Even if `LawfulLens L` failed, return `none` after letting caller report missing paths
      return none

/-- Collect missing-write dot-paths for error reporting even when `Modifies L` cannot convert
from `ReflTransGen`. -/
private def collectMissingPathsOnly (L s' s : Expr) (subFrames : Array SubstateFrame) :
    MetaM (Array Expr) := do
  let res? ← commitWhenSomeNoEx? do
    let some res ← diffConcrete s' s (some L) (allowMissing := true) subFrames #[] s' s
      | return none
    match res with
    | .diffed _ _ true missing =>
      if missing.isEmpty then return none
      return some (missing.map (·.path))
    | _ => return none
  return res?.getD #[]

/-! ### 5. Engine B — Context Frame-Algebra Graph Search -/

private inductive EdgeKind where
  | eq (prf : Expr)                    -- `from = to`
  | modifies (w : Expr) (prf : Expr)   -- `Modifies w from to`
  | rtModifies (w : Expr) (prf : Expr) -- `ReflTransGen (Modifies w) from to`
  | eqOn (g : Expr) (prf : Expr)       -- `g.get from = g.get to`
  | eqOnAll (gs : Expr) (prf : Expr)   -- `EqOnAll gs from to`
  deriving Inhabited

private structure GraphEdge where
  toIdx : Nat
  kind : EdgeKind
  deriving Inhabited

private structure StateGraph where
  sTy : Expr
  nodes : Array Expr
  adj : Array (Array GraphEdge)
  subFrames : Array SubstateFrame

private def StateGraph.findOrAdd (g : StateGraph) (e : Expr) : MetaM (StateGraph × Nat) := do
  let e := (← instantiateMVars e).consumeMData
  for i in [0:g.nodes.size] do
    if ← nodeDefEq g.nodes[i]! e then
      return (g, i)
  let idx := g.nodes.size
  return ({ g with nodes := g.nodes.push e, adj := g.adj.push #[] }, idx)

private def StateGraph.addEdge (g : StateGraph) (fromIdx toIdx : Nat) (kind : EdgeKind) :
    StateGraph :=
  if fromIdx == toIdx then g
  else { g with adj := g.adj.modify fromIdx (·.push { toIdx, kind }) }

/-- Collect candidate base state expressions of type `sTy` referenced inside a raw structure
update expression `e` (via projections or `Lens.get`). -/
private partial def findStructBaseCandidates (sTy : Expr) (e : Expr) (depth : Nat := 8) :
    MetaM (Array Expr) := do
  if depth == 0 then return #[]
  let e := (← instantiateMVars e).consumeMData
  let mut out : Array Expr := #[]
  let addCand (arr : Array Expr) (c : Expr) : MetaM (Array Expr) := do
    for x in arr do
      if ← nodeDefEq x c then return arr
    return arr.push c

  if let .letE _ _ val body _ := e then
    for c in ← findStructBaseCandidates sTy val (depth - 1) do
      out ← addCand out c
    for c in ← findStructBaseCandidates sTy (body.instantiate1 val) (depth - 1) do
      out ← addCand out c
    return out

  if let .proj _ _ base := e then
    if ← isDefEq (← inferType base) sTy then
      out ← addCand out base
    else
      for c in ← findStructBaseCandidates sTy base (depth - 1) do
        out ← addCand out c
    return out

  if e.isAppOfArity ``Optic.Lens.get 4 || e.isAppOfArity ``Optic.Lens.view 4 then
    let base := e.getArg! 3
    if ← isDefEq (← inferType base) sTy then
      out ← addCand out base
    else
      for c in ← findStructBaseCandidates sTy base (depth - 1) do
        out ← addCand out c
    return out

  if e.isAppOfArity ``Optic.Lens.set 5 then
    let base := e.getArg! 3
    if ← isDefEq (← inferType base) sTy then
      out ← addCand out base
    for c in ← findStructBaseCandidates sTy base (depth - 1) do
      out ← addCand out c
    return out

  if e.isAppOfArity ``Optic.Lens.over 5 then
    let base := e.getArg! 4
    if ← isDefEq (← inferType base) sTy then
      out ← addCand out base
    for c in ← findStructBaseCandidates sTy base (depth - 1) do
      out ← addCand out c
    return out

  if let some c := e.getAppFn.constName? then
    let env ← getEnv
    if let some pinfo ← getProjectionFnInfo? c then
      let args := e.getAppArgs
      if pinfo.numParams < args.size && args.size == pinfo.numParams + 1 then
        let base := args[pinfo.numParams]!
        if ← isDefEq (← inferType base) sTy then
          out ← addCand out base
        else
          for cand in ← findStructBaseCandidates sTy base (depth - 1) do
            out ← addCand out cand
        return out
    if let some (.ctorInfo ctorInfo) := env.find? c then
      let args := e.getAppArgs
      for i in [ctorInfo.numParams:args.size] do
        for cand in ← findStructBaseCandidates sTy args[i]! (depth - 1) do
          out ← addCand out cand
      return out
  return out

/-- Check whether expression `e` looks like a concrete update (`Lens.set`, `Lens.over`,
`pipe`/`setOf`/`overOf`, or a structure constructor). -/
private def isConcreteUpdateExpr (e : Expr) : MetaM Bool := do
  let ne ← whnfStateExpr e (unfoldLetFVar := false)
  if ne.isAppOfArity ``Optic.Lens.set 5 || ne.isAppOfArity ``Optic.Lens.over 5 then
    return true
  return (← matchStructCtorApp? ne).isSome

/-- Add a bidirectional `Modifies` / `ReflTransGen (Modifies _)` edge (reverse direction added
whenever `FactorsLawful w` or `LawfulLens w` holds). -/
private def addModifiesEdges (g : StateGraph) (u v : Nat) (w prf : Expr) (isRt : Bool) :
    MetaM StateGraph := do
  let mut g := g
  if isRt then
    g := g.addEdge u v (.rtModifies w prf)
    if let some fl ← synthFactorsLawful? w then
      let sym ← mkAppOptM ``Optic.Modifies.rt_symm
        #[none, none, some w, some fl, none, none, some prf]
      g := g.addEdge v u (.rtModifies w sym)
  else
    g := g.addEdge u v (.modifies w prf)
    if let some hl ← proveLawfulLens? w then
      let sym ← mkAppOptM ``Optic.Modifies.symm
        #[none, none, some w, some hl, none, none, some prf]
      g := g.addEdge v u (.modifies w sym)
    else if let some fl ← synthFactorsLawful? w then
      let single ← mkAppM ``Optic.Modifies.rt_single #[prf]
      let sym ← mkAppOptM ``Optic.Modifies.rt_symm
        #[none, none, some w, some fl, none, none, some single]
      g := g.addEdge v u (.rtModifies w sym)
  return g

/-- Build the state graph on type `sTy` from `initNodes`, all local-context `let`s, `Eq`,
`Modifies`, `ReflTransGen (Modifies _)`, `EqOn`, `EqOnAll`, substate frames, concrete
updates, and `fvar = rhs` `congrArg` rewrites. -/
private def buildStateGraph (sTy : Expr) (initNodes : Array Expr) (tgtL? : Option Expr) :
    MetaM StateGraph := do
  let subFrames ← collectSubstateFrames
  let mut g : StateGraph := { sTy, nodes := #[], adj := #[], subFrames }
  for n in initNodes do
    let (g', _) ← g.findOrAdd n
    g := g'

  -- Also collect `fvar = rhs` equalities (on any non-Prop type) for `congrArg` rewriting
  let mut fvarEqs : Array (FVarId × Expr × Expr) := #[]

  for decl in (← getLCtx) do
    if decl.isImplementationDetail then continue
    if decl.isLet then
      if ← isDefEq decl.type sTy then
        let x := decl.toExpr
        let val := decl.value
        let (g', u) ← g.findOrAdd x
        let (g'', v) ← g'.findOrAdd val
        let rflFwd ← mkExpectedTypeHint (← mkEqRefl x) (← mkEq x val)
        let rflBwd ← mkExpectedTypeHint (← mkEqRefl x) (← mkEq val x)
        g := (g''.addEdge u v (.eq rflFwd)).addEdge v u (.eq rflBwd)
      continue

    let conjuncts ← collectConjuncts decl.toExpr
    for (dt, prf) in conjuncts do
      if let some (ty, w, dst, src) := matchRtModifies? dt then
        if ← isDefEq ty sTy then
          let (g', u) ← g.findOrAdd dst
          let (g'', v) ← g'.findOrAdd src
          g ← addModifiesEdges g'' u v w prf (isRt := true)
      else if let some (ty, w, dst, src) := matchModifies? dt then
        if ← isDefEq ty sTy then
          let (g', u) ← g.findOrAdd dst
          let (g'', v) ← g'.findOrAdd src
          g ← addModifiesEdges g'' u v w prf (isRt := false)
      else if let some (ty, gt, dst, src) := matchEqOn? dt then
        if ← isDefEq ty sTy then
          let (g', u) ← g.findOrAdd dst
          let (g'', v) ← g'.findOrAdd src
          let sym ← mkAppM ``Optic.EqOn.symm #[prf]
          g := (g''.addEdge u v (.eqOn gt prf)).addEdge v u (.eqOn gt sym)
      else if let some (ty, gs, dst, src) := matchEqOnAll? dt then
        if ← isDefEq ty sTy then
          let (g', u) ← g.findOrAdd dst
          let (g'', v) ← g'.findOrAdd src
          let sym ← mkAppM ``Optic.EqOnAll.symm #[prf]
          g := (g''.addEdge u v (.eqOnAll gs prf)).addEdge v u (.eqOnAll gs sym)
      else if let some (ty, a, b) := dt.eq? then
        if ← isDefEq ty sTy then
          let (g', u) ← g.findOrAdd a
          let (g'', v) ← g'.findOrAdd b
          let sym ← mkEqSymm prf
          g := (g''.addEdge u v (.eq prf)).addEdge v u (.eq sym)
        -- Record `fvar = rhs` / `rhs = fvar` for `congrArg` rewriting on concrete nodes
        if !(← isProp ty) then
          let a' := a.consumeMData
          let b' := b.consumeMData
          if a'.isFVar && !b'.containsFVar a'.fvarId! then
            fvarEqs := fvarEqs.push (a'.fvarId!, b', prf)
          if b'.isFVar && !a'.containsFVar b'.fvarId! then
            fvarEqs := fvarEqs.push (b'.fvarId!, a', ← mkEqSymm prf)

  -- Expand concrete updates and `congrArg` rewrites (bounded worklist)
  let mut nextIdx : Nat := 0
  let maxNodes : Nat := 64
  while nextIdx < g.nodes.size && g.nodes.size < maxNodes do
    let u := nextIdx
    nextIdx := nextIdx + 1
    let nodeExpr := g.nodes[u]!
    let ne ← whnfStateExpr nodeExpr (unfoldLetFVar := false)

    -- A. `Lens.set l base v` / `Lens.over l f base`
    if ne.isAppOfArity ``Optic.Lens.set 5 then
      let l := ne.getArg! 2
      let base := ne.getArg! 3
      let val := ne.getArg! 4
      let (g', vIdx) ← g.findOrAdd base
      g := g'
      let stepPrf ← mkExpectedTypeHint (← mkAppM ``Optic.Modifies.set #[l, base, val])
        (← mkAppM ``Optic.Modifies #[l, nodeExpr, base])
      g ← addModifiesEdges g u vIdx l stepPrf (isRt := false)
      -- Also check substate lifting on `val` against `l.get base`!
      let oldVal ← mkAppM ``Optic.Lens.get #[l, base]
      let oldValNorm ← normalizeOpticView oldVal
      let valNorm ← normalizeOpticView val
      let valTy ← inferType val
      -- Direct single-pass `Modifies.lift` (requires neither `LawfulLens l` nor `LawfulLens innerW`)
      for sf in subFrames do
        if !sf.isRt then
          if let some innerW := sf.w? then
            if ← isDefEq sf.stateTy valTy then
              let sfDst ← normalizeOpticView sf.dst
              let sfSrc ← normalizeOpticView sf.src
              if (← withReducible (isDefEq sfDst valNorm)) &&
                 (← withReducible (isDefEq sfSrc oldValNorm)) then
                let liftedW ← mkAppM ``Optic.Lens.comp #[l, innerW]
                let liftedPrf ← mkAppM ``Optic.Modifies.lift #[l, sf.prf]
                let liftedPrf ← mkExpectedTypeHint liftedPrf
                  (← mkAppM ``Optic.Modifies #[liftedW, nodeExpr, base])
                g ← addModifiesEdges g u vIdx liftedW liftedPrf (isRt := false)
      -- General `ReflTransGen` substate lifting via `Modifies.rt_lift` + flattening
      if let some _ ← proveLawfulLens? l then
        let lSegs ← splitCompChain l
        if let some (subW, subPrf) ← findSubstateFrame? subFrames valTy val oldVal lSegs tgtL? then
          if let some (liftedW, liftedPrf) ← rtLiftFlatten? l subW subPrf then
            let modRel ← mkAppM ``Optic.Modifies #[liftedW]
            let liftedPrf ← mkExpectedTypeHint liftedPrf
              (← mkAppM ``Optic.ReflTransGen #[modRel, nodeExpr, base])
            g ← addModifiesEdges g u vIdx liftedW liftedPrf (isRt := true)
    else if ne.isAppOfArity ``Optic.Lens.over 5 then
      let l := ne.getArg! 2
      let fn := ne.getArg! 3
      let base := ne.getArg! 4
      let (g', vIdx) ← g.findOrAdd base
      g := g'
      let stepPrf ← mkExpectedTypeHint (← mkAppM ``Optic.Modifies.over #[l, fn, base])
        (← mkAppM ``Optic.Modifies #[l, nodeExpr, base])
      g ← addModifiesEdges g u vIdx l stepPrf (isRt := false)
    else if (← matchStructCtorApp? ne).isSome then
      -- B. Raw structure constructor update `{ base with ... }` (with nested substate lifting!)
      let mut cands ← findStructBaseCandidates sTy ne
      for initN in initNodes do
        unless ← nodeDefEq initN nodeExpr do
          let mut seen := false
          for c in cands do
            if ← nodeDefEq c initN then seen := true; break
          if !seen then cands := cands.push initN
      for base in cands do
        if let some res ← diffConcrete nodeExpr base tgtL? (allowMissing := false) subFrames #[] nodeExpr base then
          let (g', vIdx) ← g.findOrAdd base
          g := g'
          match res with
          | .unchanged =>
            let hEq ← mkExpectedTypeHint (← mkEqRefl nodeExpr) (← mkEq nodeExpr base)
            let hSym ← mkEqSymm hEq
            g := (g.addEdge u vIdx (.eq hEq)).addEdge vIdx u (.eq hSym)
          | .diffed usedL prf _ _ =>
            g ← addModifiesEdges g u vIdx usedL prf (isRt := true)

    -- C. `congrArg` rewriting for concrete expressions containing an `fvar` with `fvar = rhs`
    if !nodeExpr.isFVar && g.nodes.size < maxNodes then
      for (fvId, rhs, hEq) in fvarEqs do
        if nodeExpr.containsFVar fvId && g.nodes.size < maxNodes then
          let fvExpr := mkFVar fvId
          let rewritten := nodeExpr.replaceFVar fvExpr rhs
          if !(← nodeDefEq nodeExpr rewritten) then
            let fn ← mkLambdaFVars #[fvExpr] nodeExpr
            let congPrf? ← commitWhenSomeNoEx? do
              let p ← mkCongrArg fn hEq
              let expected ← mkEq nodeExpr rewritten
              if ← isDefEq (← inferType p) expected then
                return some (← mkExpectedTypeHint p expected)
              return none
            if let some congPrf := congPrf? then
              let (g', vIdx) ← g.findOrAdd rewritten
              let symPrf ← mkEqSymm congPrf
              g := (g'.addEdge u vIdx (.eq congPrf)).addEdge vIdx u (.eq symPrf)

  return g

/-- A refined step along a path from `fromNode` to `toNode` for target write-set `L`. -/
private inductive FrameStep where
  | eq (prf : Expr)               -- `fromNode = toNode`
  | rt (prf : Expr)               -- `ReflTransGen (Modifies L) fromNode toNode`
  | singleMod (w prf : Expr)      -- `Modifies w fromNode toNode` (also has `rtPrf`)
      (rtPrf : Expr)
  deriving Inhabited

/-- Check if a graph edge refines target write-set `L`, producing a `FrameStep` if so. -/
private def refineGraphEdge? (L fromNode toNode : Expr) (e : GraphEdge) :
    MetaM (Option FrameStep) := do
  match e.kind with
  | .eq prf => return some (.eq prf)
  | .modifies w prf =>
    if let some rtPrf ← refineModifiesToRt? w L fromNode toNode prf then
      return some (.singleMod w prf rtPrf)
    return none
  | .rtModifies w prf =>
    if let some rtPrf ← refineRtModifies? w L prf then
      return some (.rt rtPrf)
    return none
  | .eqOn _ _ | .eqOnAll _ _ => return none

/-- Fold a sequence of `FrameStep`s along `v₀ → v₁ → … → vₖ` into
`ReflTransGen (Modifies L) v₀ vₖ`. -/
private def foldFrameStepsToRt (L : Expr)
    (steps : Array (Nat × Nat × FrameStep)) (srcNode : Expr) : MetaM Expr := do
  let modRel ← mkAppM ``Optic.Modifies #[L]
  let rtRel ← mkAppM ``Optic.ReflTransGen #[modRel]
  let mut acc? : Option Expr := none
  for i in [0:steps.size] do
    let (_, _, step) := steps[steps.size - 1 - i]!
    match step with
    | .eq hEq =>
      match acc? with
      | none =>
        acc? := some (← rtOfEq modRel srcNode hEq)
      | some acc =>
        acc? := some (← transportLeft rtRel srcNode hEq acc)
    | .rt hRt | .singleMod _ _ hRt =>
      match acc? with
      | none => acc? := some hRt
      | some acc => acc? := some (← mkAppM ``Optic.ReflTransGen.trans #[hRt, acc])
  match acc? with
  | some prf => return prf
  | none => mkAppOptM ``Optic.ReflTransGen.refl #[none, some modRel, some srcNode]

/-- Try folding `steps` directly into single-pass `Modifies L dst src` without requiring
`LawfulLens L` when there is at most one `Modifies` step (plus any number of `Eq` steps). -/
private def tryFoldStepsDirectModifies? (L : Expr) (nodes : Array Expr)
    (steps : Array (Nat × Nat × FrameStep)) (srcNode : Expr) : MetaM (Option Expr) := do
  let modRel ← mkAppM ``Optic.Modifies #[L]
  let mut modIdx? : Option Nat := none
  let mut modCount : Nat := 0
  for i in [0:steps.size] do
    match steps[i]!.2.2 with
    | .eq _ => pure ()
    | .singleMod _ _ _ => modCount := modCount + 1; modIdx? := some i
    | .rt _ => return none
  if modCount == 0 then
    -- Pure `Eq` path
    let mut eqPrf ← mkEqRefl srcNode
    for i in [0:steps.size] do
      let (_, _, step) := steps[steps.size - 1 - i]!
      if let .eq hEq := step then
        eqPrf ← mkEqTrans hEq eqPrf
    if let some fl ← synthFactorsLawful? L then
      let base ← mkAppOptM ``Optic.Modifies.refl_of_factorsLawful
        #[none, none, some L, some fl, some srcNode]
      return some (← transportLeft modRel srcNode eqPrf base)
    return none
  if modCount == 1 then
    let idx := modIdx?.get!
    let (uIdx, vIdx, step) := steps[idx]!
    let .singleMod w prf _ := step | return none
    let some fAtom ← proveAtomicModifiesRefines? w L | return none
    let uNode := nodes[uIdx]!
    let vNode := nodes[vIdx]!
    let mut cur : Expr := mkApp3 fAtom uNode vNode prf  -- `Modifies L uNode vNode`
    -- Transport right along `vNode = ... = srcNode`
    for j in [(idx + 1):steps.size] do
      if let .eq hEq := steps[j]!.2.2 then
        cur ← transportRight modRel uNode hEq cur
    -- Transport left along `dstNode = ... = uNode`
    for k in [0:idx] do
      let j := idx - 1 - k
      if let .eq hEq := steps[j]!.2.2 then
        cur ← transportLeft modRel srcNode hEq cur
    return some cur
  return none

/-- Run BFS in `g` from `startIdx` following only edges that refine `L`, returning
`(visited, parentMap)`. If `stopIdx? = some goalIdx`, stops as soon as `goalIdx` is reached. -/
private def bfsFrame (g : StateGraph) (L : Expr) (startIdx : Nat) (stopIdx? : Option Nat) :
    MetaM (Array Bool × Array (Option (Nat × FrameStep))) := do
  let n := g.nodes.size
  let mut visited : Array Bool := Array.replicate n false
  let mut parent : Array (Option (Nat × FrameStep)) := Array.replicate n none
  visited := visited.set! startIdx true
  let mut queue : Array Nat := #[startIdx]
  let mut qHead : Nat := 0
  while qHead < queue.size do
    let u := queue[qHead]!
    qHead := qHead + 1
    if stopIdx? == some u then break
    for edge in g.adj[u]! do
      if visited[edge.toIdx]! then continue
      if let some step ← refineGraphEdge? L g.nodes[u]! g.nodes[edge.toIdx]! edge then
        visited := visited.set! edge.toIdx true
        parent := parent.set! edge.toIdx (some (u, step))
        if stopIdx? == some edge.toIdx then
          return (visited, parent)
        queue := queue.push edge.toIdx
  return (visited, parent)

/-- Reconstruct path `(u, v, step)` from `startIdx` to `endIdx` using BFS `parent` array. -/
private def reconstructPath (parent : Array (Option (Nat × FrameStep))) (startIdx endIdx : Nat) :
    Option (Array (Nat × Nat × FrameStep)) := Id.run do
  let mut rev : Array (Nat × Nat × FrameStep) := #[]
  let mut cur := endIdx
  while cur != startIdx do
    let some (p, step) := parent[cur]! | return none
    rev := rev.push (p, cur, step)
    cur := p
  return some rev.reverse

/-- Engine B solver: builds the context state graph on `sTy`, searches for a path `dst ↝ src`
valid under write-set `L` (with concrete-diff bridge fallback for `st is { s₀ with … except … }`),
and builds the `ReflTransGen (Modifies L)` or `Modifies L` proof. -/
private def engineBSolve? (sTy L dst src : Expr) (isRt : Bool) : MetaM (Option Expr) := do
  let g ← buildStateGraph sTy #[dst, src] (some L)
  let (g, dstIdx) ← g.findOrAdd dst
  let (g, srcIdx) ← g.findOrAdd src
  if dstIdx == srcIdx then
    return none  -- Already handled by reflexivity fast path

  let (visitedFwd, parentFwd) ← bfsFrame g L dstIdx (some srcIdx)
  if visitedFwd[srcIdx]! then
    let some steps := reconstructPath parentFwd dstIdx srcIdx | return none
    if !isRt then
      if let some direct ← tryFoldStepsDirectModifies? L g.nodes steps src then
        let expected ← mkAppM ``Optic.Modifies #[L, dst, src]
        return some (← mkExpectedTypeHint direct expected)
    let hRt ← foldFrameStepsToRt L steps src
    let modRel ← mkAppM ``Optic.Modifies #[L]
    let hRt ← mkExpectedTypeHint hRt (← mkAppM ``Optic.ReflTransGen #[modRel, dst, src])
    if isRt then
      return some hRt
    else
      return ← rtToSingleModifies? L dst src hRt

  -- Bridge fallback (e.g., `st = {ₗ s₀ with z := true, pc := 16 }` vs `{ₗ s₀ with pc := 16 }`):
  -- Find forward-reachable nodes from `dst` and backward-reachable nodes from `src`, and test
  -- Engine A concrete diff between concrete pairs `(u, v)`.
  let (visitedBwd, parentBwd) ← bfsFrame g L srcIdx none
  let mut fwdNodes : Array Nat := #[]
  let mut bwdNodes : Array Nat := #[]
  for i in [0:g.nodes.size] do
    if visitedFwd[i]! then fwdNodes := fwdNodes.push i
    if visitedBwd[i]! then bwdNodes := bwdNodes.push i

  for uIdx in fwdNodes do
    let uExpr := g.nodes[uIdx]!
    let uConc ← isConcreteUpdateExpr uExpr
    for vIdx in bwdNodes do
      if uIdx == vIdx then continue
      let vExpr := g.nodes[vIdx]!
      let vConc ← isConcreteUpdateExpr vExpr
      unless uConc || vConc do continue
      if let some bridgeRt ← engineASolve? L uExpr vExpr (isRt := true) g.subFrames then
        -- Assemble `dst ↝ uIdx` + `bridgeRt : uIdx ↝ vIdx` + `(src ↝ vIdx)⁻¹`
        let some path1 := reconstructPath parentFwd dstIdx uIdx | continue
        let some path2Fwd := reconstructPath parentBwd srcIdx vIdx | continue
        -- Reverse `path2Fwd : src ↝ vIdx` into `vIdx ↝ src`
        let mut path2Rev : Option (Array (Nat × Nat × FrameStep)) := some #[]
        for k in [0:path2Fwd.size] do
          let (a, b, step) := path2Fwd[path2Fwd.size - 1 - k]!
          let revStep? ← match step with
            | .eq hEq => pure (some (.eq (← mkEqSymm hEq)))
            | .rt hRt | .singleMod _ _ hRt =>
              if let some fl ← synthFactorsLawful? L then
                let sym ← mkAppOptM ``Optic.Modifies.rt_symm
                  #[none, none, some L, some fl, none, none, some hRt]
                pure (some (.rt sym))
              else
                pure none
          match path2Rev, revStep? with
          | some acc, some rs => path2Rev := some (acc.push (b, a, rs))
          | _, _ => path2Rev := none; break
        if let some p2 := path2Rev then
          let fullSteps := path1 ++ #[(uIdx, vIdx, .rt bridgeRt)] ++ p2
          let hRt ← foldFrameStepsToRt L fullSteps src
          let modRel ← mkAppM ``Optic.Modifies #[L]
          let hRt ← mkExpectedTypeHint hRt (← mkAppM ``Optic.ReflTransGen #[modRel, dst, src])
          if isRt then
            return some hRt
          else
            return ← rtToSingleModifies? L dst src hRt

  return none

/-! ### 6. Engine C — Preservation & Narrowing (`EqOn` / `EqOnAll`) -/

/-- Extract the underlying `Getter S A` from an `AnyGetter S` (including `ToAnyGetter.toAnyGetter …`). -/
private def extractGetter (anyG : Expr) : MetaM Expr := do
  let anyG' ← whnf (← instantiateMVars anyG)
  if anyG'.isAppOfArity ``Optic.AnyGetter.of 3 then
    return anyG'.getArg! 2
  let g ← mkAppM ``Optic.AnyGetter.getter #[anyG]
  whnfOptic g

/-- Check whether `targetG : Getter S A` occurs in a literal `List (AnyGetter S)` `gs`, returning
a proof of `anyG ∈ gs` together with `anyG` if found. -/
private partial def findGetterInList? (gs targetG : Expr) : MetaM (Option (Expr × Expr)) := do
  let ngs ← whnf (← instantiateMVars gs)
  if ngs.isAppOfArity ``List.cons 3 then
    let elemTy := ngs.getArg! 0
    let hd := ngs.getArg! 1
    let tl := ngs.getArg! 2
    let hdGetter ← extractGetter hd
    if ← commitWhen (isDefEq hdGetter targetG) then
      let hMem ← mkAppOptM ``List.mem_cons_self #[some elemTy, some hd, some tl]
      return some (hd, hMem)
    if let some (found, hTl) ← findGetterInList? tl targetG then
      let hMem ← mkAppOptM ``List.mem_cons_of_mem #[some elemTy, some hd, some found, some tl, some hTl]
      return some (found, hMem)
  return none

/-- Try to prove `g.get fromNode = g.get toNode` across a single graph edge. -/
private def proveEdgePreservesGetter? (g : Expr) (edge : GraphEdge) : MetaM (Option Expr) := do
  match edge.kind with
  | .eq hEq =>
    let getFn ← mkAppM ``Optic.Getter.get #[g]
    return some (← mkCongrArg getFn hEq)
  | .modifies w hMod =>
    if let some hInd ← proveIndependent? w g then
      return some (← mkAppM ``Optic.Modifies.preserves #[hInd, hMod])
    return none
  | .rtModifies w hRt =>
    if let some hInd ← proveIndependent? w g then
      return some (← mkAppM ``Optic.Modifies.rt_preserves #[hInd, hRt])
    return none
  | .eqOn g' hEqOn =>
    if ← commitWhen (isDefEq g' g) then
      return some hEqOn
    return none
  | .eqOnAll gs hAll =>
    if let some (_, hMem) ← findGetterInList? gs g then
      return some (← mkAppM ``Optic.EqOnAll.of_mem #[hAll, hMem])
    return none

/-- Prove `g.get dst = g.get src` using:
1. `with_reducible rfl`,
2. direct local-context equality,
3. BFS over `graph` chaining `Eq.trans` via `proveIndependent?` + `Modifies.rt_preserves` /
   `Modifies.preserves` / `congrArg` / `EqOn` / `EqOnAll`. -/
private def proveGetterEq? (graph : StateGraph) (g dst src : Expr) : MetaM (Option Expr) := do
  let lhs ← mkAppM ``Optic.Getter.get #[g, dst]
  let rhs ← mkAppM ``Optic.Getter.get #[g, src]
  let eqGoal ← mkEq lhs rhs

  -- 1. Fast path: `with_reducible rfl`
  if ← withReducible (isDefEq lhs rhs) then
    return some (← mkExpectedTypeHint (← mkEqRefl lhs) eqGoal)

  -- 2. Direct equality in local context (including `Eq.symm`)
  let lhsNorm ← normalizeOpticView lhs
  let rhsNorm ← normalizeOpticView rhs
  for decl in (← getLCtx) do
    if decl.isImplementationDetail || decl.isLet then continue
    let conjuncts ← collectConjuncts decl.toExpr
    for (dt, prf) in conjuncts do
      if let some (_, a, b) := dt.eq? then
        let aNorm ← normalizeOpticView a
        let bNorm ← normalizeOpticView b
        if (← withReducible (isDefEq aNorm lhsNorm)) && (← withReducible (isDefEq bNorm rhsNorm)) then
          return some (← mkExpectedTypeHint prf eqGoal)
        if (← withReducible (isDefEq aNorm rhsNorm)) && (← withReducible (isDefEq bNorm lhsNorm)) then
          return some (← mkExpectedTypeHint (← mkEqSymm prf) eqGoal)

  -- 3. BFS in `graph` from `dst` to `src`
  let (graph, dstIdx) ← graph.findOrAdd dst
  let (graph, srcIdx) ← graph.findOrAdd src
  if dstIdx == srcIdx then
    return some (← mkExpectedTypeHint (← mkEqRefl lhs) eqGoal)

  let n := graph.nodes.size
  let mut visited : Array Bool := Array.replicate n false
  let mut parent : Array (Option (Nat × Expr)) := Array.replicate n none
  visited := visited.set! dstIdx true
  let mut queue : Array Nat := #[dstIdx]
  let mut qHead : Nat := 0
  let mut found := false
  while qHead < queue.size && !found do
    let u := queue[qHead]!
    qHead := qHead + 1
    for edge in graph.adj[u]! do
      if visited[edge.toIdx]! then continue
      if let some stepEq ← proveEdgePreservesGetter? g edge then
        visited := visited.set! edge.toIdx true
        parent := parent.set! edge.toIdx (some (u, stepEq))
        if edge.toIdx == srcIdx then
          found := true
          break
        queue := queue.push edge.toIdx

  unless found do return none

  -- Reconstruct chain of `Eq.trans` from `dstIdx` to `srcIdx`
  let mut revEqs : Array Expr := #[]
  let mut cur := srcIdx
  while cur != dstIdx do
    let some (p, stepEq) := parent[cur]! | return none
    revEqs := revEqs.push stepEq
    cur := p
  let eqs := revEqs.reverse
  if eqs.isEmpty then
    return some (← mkExpectedTypeHint (← mkEqRefl lhs) eqGoal)
  let mut acc := eqs[0]!
  for i in [1:eqs.size] do
    acc ← mkEqTrans acc eqs[i]!
  return some (← mkExpectedTypeHint acc eqGoal)

/-- Split `EqOnAll gs dst src` via `EqOnAll.cons` / `EqOnAll.nil`, proving each getter
using `proveGetterEq?` and collecting any unproved getter equality subgoals. -/
private partial def solveEqOnAllAux (graph : StateGraph) (gs dst src : Expr) :
    MetaM (Option (Expr × Array MVarId)) := do
  -- Fast path: `EqOnAll.refl`
  if ← withReducible (isDefEq dst src) then
    let prf ← mkAppM ``Optic.EqOnAll.refl #[gs, src]
    let expected ← mkAppM ``Optic.EqOnAll #[gs, dst, src]
    return some (← mkExpectedTypeHint prf expected, #[])

  -- Check direct `EqOnAll gs` hypothesis in context (especially for non-literal `gs`)
  let targetTy ← mkAppM ``Optic.EqOnAll #[gs, dst, src]
  for decl in (← getLCtx) do
    if decl.isImplementationDetail || decl.isLet then continue
    let conjuncts ← collectConjuncts decl.toExpr
    for (dt, prf) in conjuncts do
      if let some (_, gs', a, b) := matchEqOnAll? dt then
        if ← withReducible (isDefEq gs' gs) then
          if (← withReducible (isDefEq a dst)) && (← withReducible (isDefEq b src)) then
            return some (← mkExpectedTypeHint prf targetTy, #[])
          if (← withReducible (isDefEq a src)) && (← withReducible (isDefEq b dst)) then
            let sym ← mkAppM ``Optic.EqOnAll.symm #[prf]
            return some (← mkExpectedTypeHint sym targetTy, #[])

  let ngs ← whnf (← instantiateMVars gs)
  if ngs.isAppOfArity ``List.nil 1 then
    let elemTy ← whnf (ngs.getArg! 0)
    let .const _ anyLvls := elemTy.getAppFn | return none
    let prf := mkApp3 (mkConst ``Optic.EqOnAll.nil anyLvls) graph.sTy dst src
    return some (← mkExpectedTypeHint prf targetTy, #[])

  if ngs.isAppOfArity ``List.cons 3 then
    let hd := ngs.getArg! 1
    let tl := ngs.getArg! 2
    let g ← extractGetter hd
    let lhs ← mkAppM ``Optic.Getter.get #[g, dst]
    let rhs ← mkAppM ``Optic.Getter.get #[g, src]
    let eqTy ← mkEq lhs rhs

    let (hdPrf, hdOpen) ← match ← proveGetterEq? graph g dst src with
      | some p => pure (p, #[])
      | none =>
        let mvar ← mkFreshExprMVar eqTy
        pure (mvar, #[mvar.mvarId!])

    let some (tlPrf, tlOpen) ← solveEqOnAllAux graph tl dst src | return none
    let prf ← mkAppOptM ``Optic.EqOnAll.cons
      #[none, some hd, some tl, some dst, some src, some hdPrf, some tlPrf]
    return some (← mkExpectedTypeHint prf targetTy, hdOpen ++ tlOpen)

  return none

/-! ### 7. User-Facing `lens_frame` Tactic -/

/-- Solve framing goals (`ReflTransGen (Modifies _)`, `Modifies _`, `EqOn`, `EqOnAll`),
including `≡ₚ … except […]`, `≡ₚ … on […]`, and `st is { s₀ with … except … }`:
1. Engine A: symbolic diff of concrete lens & raw structure updates (1-step fast path +
   recursive diff + substate lifting + missing-write diagnostics with focused subgoals).
2. Engine B: context frame-algebra graph search (permutation, weakening, deduplication,
   symmetry, transitivity, coarsening, and substate lifting with zero `Disjoint` under
   `ReflTransGen`).
3. Engine C: getter preservation & narrowing (`EqOn` / `EqOnAll`), leaving any unproved
   getter equalities open. -/
elab "lens_frame" : tactic => withMainContext do
  let g ← getMainGoal
  let rawTarget := (← instantiateMVars (← g.getType)).consumeMData
  let target ←
    if isFrameGoal rawTarget then pure rawTarget
    else withReducible (whnf rawTarget)

  -- Case 1 & 2: `ReflTransGen (Modifies L) dst src` or `Modifies L dst src`
  let frameSpec? : Option (Expr × Expr × Expr × Expr × Bool) :=
    match matchRtModifies? target with
    | some (sTy, l, dst, src) => some (sTy, l, dst, src, true)
    | none =>
      match matchModifies? target with
      | some (sTy, l, dst, src) => some (sTy, l, dst, src, false)
      | none => none

  if let some (sTy, L, dst, src, isRt) := frameSpec? then
    -- 0. Reflexivity fast path
    if ← withReducible (isDefEq dst src) then
      if isRt then
        let modRel ← mkAppM ``Optic.Modifies #[L]
        let prf ← mkAppOptM ``Optic.ReflTransGen.refl #[none, some modRel, some src]
        g.assign (← mkExpectedTypeHint prf rawTarget)
        return
      else if let some fl ← synthFactorsLawful? L then
        let prf ← mkAppOptM ``Optic.Modifies.refl_of_factorsLawful
          #[none, none, some L, some fl, some src]
        g.assign (← mkExpectedTypeHint prf rawTarget)
        return

    let subFrames ← collectSubstateFrames

    -- 1. Engine A (complete solve)
    if let some prf ← engineASolve? L dst src isRt subFrames then
      g.assign (← mkExpectedTypeHint prf rawTarget)
      return

    -- 2. Engine B (context frame-algebra graph search)
    if let some prf ← engineBSolve? sTy L dst src isRt then
      g.assign (← mkExpectedTypeHint prf rawTarget)
      return

    -- 3. Engine A missing-write diagnostics + focused equality subgoals
    if let some (partialPrf, missing) ← engineAMissingWrites? L dst src isRt subFrames then
      let mut names : Array String := #[]
      for mw in missing do
        let s ← formatLensPath mw.path
        unless names.contains s do
          names := names.push s
      logInfo m!"lens_frame: add to writes: [{", ".intercalate names.toList}]"
      g.assign (← mkExpectedTypeHint partialPrf rawTarget)
      replaceMainGoal (missing.map (·.mvarId)).toList
      return

    -- Even if partial proof couldn't be constructed (e.g. non-lawful `Modifies L`), still log
    -- missing writes if concrete diff identified them.
    let missingPaths ← collectMissingPathsOnly L dst src subFrames
    if !missingPaths.isEmpty then
      let mut names : Array String := #[]
      for p in missingPaths do
        let s ← formatLensPath p
        unless names.contains s do
          names := names.push s
      logInfo m!"lens_frame: add to writes: [{", ".intercalate names.toList}]"

    throwError "lens_frame: failed to prove frame goal:{indentExpr rawTarget}"

  -- Case 3: `EqOn gt dst src`
  if let some (sTy, gt, dst, src) := matchEqOn? target then
    let graph ← buildStateGraph sTy #[dst, src] none
    if let some prf ← proveGetterEq? graph gt dst src then
      g.assign (← mkExpectedTypeHint prf rawTarget)
      return
    throwError "lens_frame: failed to prove preservation:{indentExpr rawTarget}"

  -- Case 4: `EqOnAll gs dst src`
  if let some (sTy, gs, dst, src) := matchEqOnAll? target then
    let graph ← buildStateGraph sTy #[dst, src] none
    if let some (prf, openGoals) ← solveEqOnAllAux graph gs dst src then
      g.assign (← mkExpectedTypeHint prf rawTarget)
      replaceMainGoal openGoals.toList
      return
    throwError "lens_frame: failed to prove preservation frame:{indentExpr rawTarget}"

  throwError "lens_frame: expected `ReflTransGen (Modifies _)`, `Modifies`, `EqOn`, or `EqOnAll`, got:{indentExpr rawTarget}"

end Optic.Tactic

end
