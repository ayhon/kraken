module

public import Lens.Basic
public import Lens.Frame
public import Lens.ProdFrame
public import Lens.Derive
public meta import Lean

/-!
# Path-Aware Disjointness & Independence Automation (`lens_disjoint`, `lens_indep`)

Provides:
- `@[lens_disjoint]` / `@[lens_indep]`: extensible attribute tables for registering domain-specific
  `Disjoint` and `Independent` lemmas (e.g., bit-slices, custom optics) without modifying `Lens/`.
- Shared optics-aware AST utilities (`whnfOptic`, `splitCompChain`, `mkCompChain`, `splitProdTree`,
  `lensPathFromProj?`) exported in `Optic.Tactic` for downstream lens tactics (`Lens.Tactics.*`).
- `Optic.Tactic.proveDisjoint?` / `Optic.Tactic.proveIndependent?`: compositional, path-aware
  `MetaM` provers that:
  1. descend through shared `∘ₗ` prefixes (`Disjoint.comp_same`),
  2. lift divergence at distinct `make_lenses` fields without unfolding untouched sub-structures
     (`Disjoint.comp` / `comp_left` / `comp_right`),
  3. split product lenses (`Disjoint.prod_left` / `prod_right`, `Independent.prod_lens`),
  4. discharge `Lens.atKey` disjointness via local hypotheses, `decide`, or `omega`,
  5. consult `@[lens_disjoint]` / `@[lens_indep]` and local context hypotheses (modulo symmetry),
  6. prove `Independent` for arbitrary composite derived views (`Getter.of f`) by congruence-first
     AST decomposition into atomic field/map projections.
- `lens_disjoint` and `lens_indep` tactics.
-/

public meta section

open Lean Meta Elab Tactic

namespace Optic.Tactic

/-! ### Extensible Attributes (`@[lens_disjoint]`, `@[lens_indep]`) -/

/-- Scoped environment extension storing `@[lens_disjoint]` theorem names. -/
initialize lensDisjointExt : SimpleScopedEnvExtension Name (Array Name) ←
  registerSimpleScopedEnvExtension {
    name := `Optic.Tactic.lensDisjointExt
    addEntry := fun arr n => if arr.contains n then arr else arr.push n
    initial := #[]
  }

/-- Register a `Disjoint l₁ l₂` lemma for automatic use by `lens_disjoint` and downstream lens
tactics (`lens_frame`, `lens_eqs`, `lens_simp`). -/
initialize registerBuiltinAttribute {
  name := `lens_disjoint
  descr := "register a `Optic.Disjoint` theorem for `lens_disjoint` and lens framing tactics"
  add := fun declName _stx kind => do
    lensDisjointExt.add declName kind
}

/-- Scoped environment extension storing `@[lens_indep]` theorem names. -/
initialize lensIndepExt : SimpleScopedEnvExtension Name (Array Name) ←
  registerSimpleScopedEnvExtension {
    name := `Optic.Tactic.lensIndepExt
    addEntry := fun arr n => if arr.contains n then arr else arr.push n
    initial := #[]
  }

/-- Register an `Independent l g` lemma for automatic use by `lens_disjoint`/`lens_indep` and
downstream lens tactics. -/
initialize registerBuiltinAttribute {
  name := `lens_indep
  descr := "register an `Optic.Independent` theorem for `lens_disjoint` and lens framing tactics"
  add := fun declName _stx kind => do
    lensIndepExt.add declName kind
}

/-! ### Optics-Aware Head Normalization & Path Utilities -/

/-- Constants treated as opaque optic constructors by `whnfOptic` so we unfold user `abbrev`s
like `stX0` or `stRegs` into their `∘ₗ` / `×ₗ` spine without unfolding generated `make_lenses`
definitions or primitive optics. -/
private def isOpticHeadConst (env : Environment) (c : Name) : Bool :=
  c == ``Optic.Lens.comp ||
  c == ``Optic.Lens.prod ||
  c == ``Optic.Lens.id ||
  c == ``Optic.Lens.unit ||
  c == ``Optic.Lens.fst ||
  c == ``Optic.Lens.snd ||
  c == ``Optic.Lens.atKey ||
  c == ``Optic.Lens.toGetter ||
  c == ``Optic.Lens.mk ||
  c == ``Optic.Iso.toLens ||
  c == ``Optic.Iso.toGetter ||
  c == ``Optic.Iso.comp ||
  c == ``Optic.Iso.id ||
  c == ``Optic.Iso.symm ||
  c == ``Optic.Getter.of ||
  c == ``Optic.Getter.id ||
  c == ``Optic.Getter.comp ||
  c == ``Optic.Getter.map ||
  c == ``Optic.Getter.prod ||
  c == ``Optic.Getter.const ||
  (Optic.Derive.lookupLensField? env c).isSome

/-- Reduce an optic expression just enough to expose its top-level optic constructor
(`Lens.comp`, `Lens.prod`, `Lens.unit`, `Lens.atKey`, `StructName.Lenses.<field>`, etc.),
unfolding reducible user abbreviations (`abbrev stX0 := …`) and local `let`s without unfolding
`make_lenses` field lenses. -/
partial def whnfOptic (e : Expr) : MetaM Expr := do
  let e := (← instantiateMVars e).consumeMData.headBeta
  if e.isFVar then
    if let some val ← e.fvarId!.getValue? then
      return ← whnfOptic val
    return e
  if let some c := e.getAppFn.constName? then
    let env ← getEnv
    if isOpticHeadConst env c then
      return e
    if ← isReducible c then
      if let some e' ← unfoldDefinition? e then
        return ← whnfOptic e'
  return e

/-- Flatten an arbitrarily associated `Lens.comp` chain into an array of atomic segments
(dropping `Lens.id`). Because `Lens.comp` is definitionally associative, any re-association
is defeq to the original lens. -/
partial def splitCompChain (l : Expr) : MetaM (Array Expr) := do
  let l ← whnfOptic l
  if l.isAppOfArity ``Optic.Lens.id 1 then
    return #[]
  if l.isAppOfArity ``Optic.Lens.comp 5 then
    let outer := l.getArg! 3
    let inner := l.getArg! 4
    return (← splitCompChain outer) ++ (← splitCompChain inner)
  return #[l]

/-- Rebuild a non-empty array of lens segments into a right-associated `Lens.comp` chain. -/
def mkCompChain (segs : Array Expr) : MetaM Expr := do
  if segs.isEmpty then
    throwError "mkCompChain: empty lens path"
  let mut acc := segs[segs.size - 1]!
  for i in [1:segs.size] do
    let idx := segs.size - 1 - i
    acc ← mkAppM ``Optic.Lens.comp #[segs[idx]!, acc]
  return acc

/-- Flatten an arbitrarily associated `Lens.prod` tree into its leaf lenses (dropping `Lens.unit`). -/
partial def splitProdTree (l : Expr) : MetaM (Array Expr) := do
  let l ← whnfOptic l
  if l.isAppOfArity ``Optic.Lens.unit 1 then
    return #[]
  if l.isAppOfArity ``Optic.Lens.prod 5 then
    let l₁ := l.getArg! 3
    let l₂ := l.getArg! 4
    return (← splitProdTree l₁) ++ (← splitProdTree l₂)
  return #[l]

/-- Try to build a `make_lenses` lens expression for field `fieldIdx` of a value of type `structTy`. -/
def mkStructFieldLens? (structTy : Expr) (fieldIdx : Nat) : MetaM (Option Expr) := do
  let structTy ← whnf (← instantiateMVars structTy)
  let .const structName _ := structTy.getAppFn | return none
  let some info := Optic.Derive.lookupStructFieldLens? (← getEnv) structName fieldIdx
    | return none
  let params := structTy.getAppArgs[:info.numParams].toArray
  try
    let lens ← mkAppOptM info.lensName (params.map some)
    return some lens
  catch _ =>
    return none

/-- Reconstruct a `Lens` from an expression projecting out of `sVar`, supporting:
- raw structure projections `e.i`,
- structure projection functions `S.field e`,
- `Lens.get l e` / `Lens.view l e` / `Optic.Notation.viewOf e l` / `HasGet.getOf l e`,
- `Prod.fst e` / `Prod.snd e` (`Lens.fst` / `Lens.snd`),
- function application `m key` where `m` is a `k → v` projection with `[DecidableEq k]` (`Lens.atKey key`). -/
partial def lensPathFromProj? (sVar : Expr) (e : Expr) : MetaM (Option Expr) := do
  let e := (← instantiateMVars e).consumeMData
  if e == sVar then
    let sTy ← inferType sVar
    return some (← mkAppOptM ``Optic.Lens.id #[some sTy])
  unless e.containsFVar sVar.fvarId! do
    return none
  -- Raw structure projection `x.i`
  if let .proj _ idx base := e then
    let some baseLens ← lensPathFromProj? sVar base | return none
    let baseTy ← inferType base
    let some fieldLens ← mkStructFieldLens? baseTy idx | return none
    if (← whnfOptic baseLens).isAppOfArity ``Optic.Lens.id 1 then
      return some fieldLens
    return some (← mkAppM ``Optic.Lens.comp #[baseLens, fieldLens])
  -- `Optic.Lens.get l base` / `Optic.Lens.view l base`
  if e.isAppOfArity ``Optic.Lens.get 4 || e.isAppOfArity ``Optic.Lens.view 4 then
    let l := e.getArg! 2
    let base := e.getArg! 3
    if !l.containsFVar sVar.fvarId! then
      let some baseLens ← lensPathFromProj? sVar base | return none
      if (← whnfOptic baseLens).isAppOfArity ``Optic.Lens.id 1 then
        return some l
      return some (← mkAppM ``Optic.Lens.comp #[baseLens, l])
  -- `Optic.Getter.get g base` when `g = Lens.toGetter l`
  if e.isAppOfArity ``Optic.Getter.get 4 then
    let g ← whnfOptic (e.getArg! 2)
    let base := e.getArg! 3
    if !g.containsFVar sVar.fvarId! && g.isAppOfArity ``Optic.Lens.toGetter 3 then
      let l := g.getArg! 2
      let some baseLens ← lensPathFromProj? sVar base | return none
      if (← whnfOptic baseLens).isAppOfArity ``Optic.Lens.id 1 then
        return some l
      return some (← mkAppM ``Optic.Lens.comp #[baseLens, l])
  -- `HasGet.getOf o base` / `Optic.Notation.viewOf base o`
  if e.isAppOfArity ``Optic.HasGet.getOf 6 then
    let o ← whnfOptic (e.getArg! 4)
    let base := e.getArg! 5
    if !o.containsFVar sVar.fvarId! then
      let oTy ← whnf (← inferType o)
      if oTy.isAppOfArity ``Optic.Lens 2 then
        let some baseLens ← lensPathFromProj? sVar base | return none
        if (← whnfOptic baseLens).isAppOfArity ``Optic.Lens.id 1 then
          return some o
        return some (← mkAppM ``Optic.Lens.comp #[baseLens, o])
  -- `Prod.fst` / `Prod.snd`
  if e.isAppOfArity ``Prod.fst 3 then
    let base := e.getArg! 2
    let some baseLens ← lensPathFromProj? sVar base | return none
    let fstLens ← mkAppOptM ``Optic.Lens.fst #[some (e.getArg! 0), some (e.getArg! 1)]
    if (← whnfOptic baseLens).isAppOfArity ``Optic.Lens.id 1 then
      return some fstLens
    return some (← mkAppM ``Optic.Lens.comp #[baseLens, fstLens])
  if e.isAppOfArity ``Prod.snd 3 then
    let base := e.getArg! 2
    let some baseLens ← lensPathFromProj? sVar base | return none
    let sndLens ← mkAppOptM ``Optic.Lens.snd #[some (e.getArg! 0), some (e.getArg! 1)]
    if (← whnfOptic baseLens).isAppOfArity ``Optic.Lens.id 1 then
      return some sndLens
    return some (← mkAppM ``Optic.Lens.comp #[baseLens, sndLens])
  -- Structure projection function `S.field base`
  if let some c := e.getAppFn.constName? then
    if let some pinfo ← getProjectionFnInfo? c then
      let args := e.getAppArgs
      if pinfo.numParams < args.size && args.size == pinfo.numParams + 1 then
        let base := args[pinfo.numParams]!
        if let some baseLens ← lensPathFromProj? sVar base then
          let baseTy ← inferType base
          if let some fieldLens ← mkStructFieldLens? baseTy pinfo.i then
            if (← whnfOptic baseLens).isAppOfArity ``Optic.Lens.id 1 then
              return some fieldLens
            return some (← mkAppM ``Optic.Lens.comp #[baseLens, fieldLens])
    -- Also handle reducible wrappers around projections (e.g. `Optic.Notation.viewOf`)
    if ← isReducible c then
      if let some e' ← unfoldDefinition? e then
        let e' := e'.headBeta
        if e' != e then
          if let some res ← lensPathFromProj? sVar e' then
            return some res
  -- Map lookup `m key` where `m` projects out of `sVar` and `key` does not depend on `sVar`
  if let .app fn arg := e then
    if !arg.containsFVar sVar.fvarId! && fn.containsFVar sVar.fvarId! then
      let fnTy ← whnf (← inferType fn)
      if fnTy.isForall && !fnTy.bindingBody!.hasLooseBVars then
        if let some baseLens ← lensPathFromProj? sVar fn then
          let kTy := fnTy.bindingDomain!
          let vTy := fnTy.bindingBody!
          if let some decInst := (← trySynthInstance (← mkAppM ``DecidableEq #[kTy])).toOption then
            let keyLens ← mkAppOptM ``Optic.Lens.atKey #[some kTy, some vTy, some decInst, some arg]
            if (← whnfOptic baseLens).isAppOfArity ``Optic.Lens.id 1 then
              return some keyLens
            return some (← mkAppM ``Optic.Lens.comp #[baseLens, keyLens])
  return none

/-! ### Auxiliary Inequality & Side-Condition Prover -/

/-- Attempt to prove `k₁ ≠ k₂` using local hypotheses, `decide`, or `omega`. -/
def proveNe? (k₁ k₂ : Expr) : MetaM (Option Expr) := do
  let k₁ ← instantiateMVars k₁
  let k₂ ← instantiateMVars k₂
  let neGoal ← mkAppM ``Ne #[k₁, k₂]
  -- 1. Direct or symmetric match in local context
  for decl in (← getLCtx) do
    if decl.isImplementationDetail then continue
    let dt := (← instantiateMVars decl.type).consumeMData
    if ← isDefEq dt neGoal then
      return some decl.toExpr
    if dt.isAppOfArity ``Ne 3 then
      let a := dt.getArg! 1
      let b := dt.getArg! 2
      if (← isDefEq a k₂) && (← isDefEq b k₁) then
        return some (← mkAppM ``Ne.symm #[decl.toExpr])
    if dt.isAppOfArity ``Not 1 then
      let inner := (dt.getArg! 0).consumeMData
      if let some (_, a, b) := inner.eq? then
        if (← isDefEq a k₁) && (← isDefEq b k₂) then
          return some decl.toExpr
        if (← isDefEq a k₂) && (← isDefEq b k₁) then
          return some (← mkAppM ``Ne.symm #[decl.toExpr])
  -- 2. Ground `decide`
  if !k₁.hasFVar && !k₂.hasFVar && !k₁.hasExprMVar && !k₂.hasExprMVar then
    let prf? ← commitWhenSomeNoEx? do
      some <$> mkDecideProof neGoal
    if prf?.isSome then return prf?
  -- 3. `omega` for linear arithmetic inequalities (e.g. `i ≠ i + 1`)
  let mvar ← mkFreshExprMVar neGoal
  let ok ← commitWhen do
    try
      let remaining ← Elab.Term.TermElabM.run' do
        Elab.Tactic.run mvar.mvarId! do
          evalTactic (← `(tactic| omega))
      return remaining.isEmpty
    catch _ =>
      return false
  if ok then
    return some (← instantiateMVars mvar)
  return none

/-- Synthesize `LawfulLens l` if possible, returning `none` instead of throwing. -/
def synthLawfulLens? (l : Expr) : MetaM (Option Expr) := do
  let ty ← mkAppM ``Optic.LawfulLens #[l]
  return (← trySynthInstance ty).toOption

/-! ### Compositional `Disjoint` Prover (`proveDisjoint?`) -/

/-- Prove `Disjoint l₁ l₂` for two direct `make_lenses` field lenses of the *same* structure
with distinct field indices, without unfolding any inner sub-structures. -/
private def proveDistinctStructFields? (l₁ l₂ : Expr) : MetaM (Option Expr) := do
  let env ← getEnv
  let some c₁ := l₁.getAppFn.constName? | return none
  let some c₂ := l₂.getAppFn.constName? | return none
  let some info₁ := Optic.Derive.lookupLensField? env c₁ | return none
  let some info₂ := Optic.Derive.lookupLensField? env c₂ | return none
  unless info₁.structName == info₂.structName && info₁.fieldIdx != info₂.fieldIdx do
    return none
  let goalTy ← mkAppM ``Optic.Disjoint #[l₁, l₂]
  let mvar ← mkFreshExprMVar goalTy
  let ok ← commitWhen do
    try
      let (xs, g) ← mvar.mvarId!.introN 3
      -- First try pure `rfl` (works without `cases` by projection reduction!)
      let closedByRfl ← commitWhen do
        try g.refl; return true catch _ => return false
      if closedByRfl then return true
      let sgs ← g.cases xs[0]!
      for sg in sgs do
        sg.mvarId.refl
      return true
    catch _ =>
      return false
  if ok then
    return some (← instantiateMVars mvar)
  return none

/-- Try to close `goalTy` using a registered theorem `thmName` (filling remaining side conditions
via typeclass search, `proveNe?`, or local hypotheses). Uses `forallMetaTelescope` (non-reducing)
so `Optic.Disjoint` / `Optic.Independent` heads are not unfolded into their `∀ x v₁ v₂, …` bodies. -/
private def tryApplyRegistered? (thmName : Name) (goalTy : Expr)
    (subGoalSolver : Expr → MetaM (Option Expr)) : MetaM (Option Expr) :=
  commitWhenSomeNoEx? do
    let thm ← mkConstWithFreshMVarLevels thmName
    let thmTy ← inferType thm
    let (mvars, bis, body) ← forallMetaTelescope thmTy
    unless ← isDefEq body goalTy do return none
    for m in mvars, bi in bis do
      let mId := m.mvarId!
      if ← mId.isAssigned then continue
      let mTy ← instantiateMVars (← mId.getType)
      if bi.isInstImplicit then
        let some inst := (← trySynthInstance mTy).toOption | return none
        unless ← isDefEq m inst do return none
      else if ← isProp mTy then
        let some prf ← subGoalSolver mTy | return none
        unless ← isDefEq m prf do return none
      else
        return none
    for m in mvars do
      unless ← m.mvarId!.isAssigned do return none
    return some (← instantiateMVars (mkAppN thm mvars))

/-- Fallback structural `Disjoint` check by introducing `(x, v₁, v₂)` and trying `rfl` or `cases x; rfl`. -/
private def proveDisjointFallback? (l₁ l₂ : Expr) : MetaM (Option Expr) := do
  let goalTy ← mkAppM ``Optic.Disjoint #[l₁, l₂]
  let mvar ← mkFreshExprMVar goalTy
  let ok ← commitWhen do
    try
      let (xs, g) ← mvar.mvarId!.introN 3
      let closedRfl ← commitWhen do
        try g.refl; return true catch _ => return false
      if closedRfl then return true
      let sgs ← g.cases xs[0]!
      for sg in sgs do
        sg.mvarId.refl
      return true
    catch _ =>
      return false
  if ok then
    return some (← instantiateMVars mvar)
  return none

/-- Recursively prove `Optic.Disjoint l₁ l₂` using compositional path descent, diverging-field
lifting, product splitting, `atKey` inequality, `@[lens_disjoint]` lemmas, and local hypotheses. -/
partial def proveDisjoint? (l₁ l₂ : Expr) (fuel : Nat := 16) : MetaM (Option Expr) := do
  if fuel == 0 then return none
  let l₁ ← instantiateMVars l₁
  let l₂ ← instantiateMVars l₂
  let goalTy ← mkAppM ``Optic.Disjoint #[l₁, l₂]

  -- 1. Local context (direct or symmetric)
  for decl in (← getLCtx) do
    if decl.isImplementationDetail then continue
    let dt := (← instantiateMVars decl.type).consumeMData
    if dt.isAppOfArity ``Optic.Disjoint 5 then
      let a := dt.getArg! 3
      let b := dt.getArg! 4
      if (← isDefEq a l₁) && (← isDefEq b l₂) then
        return some decl.toExpr
      if (← isDefEq a l₂) && (← isDefEq b l₁) then
        return some (← mkAppM ``Optic.Disjoint.symm #[decl.toExpr])

  -- 2. Normalize optic head without unfolding generated field lenses
  let n₁ ← whnfOptic l₁
  let n₂ ← whnfOptic l₂

  -- 3. `Lens.unit`
  if n₁.isAppOfArity ``Optic.Lens.unit 1 then
    return some (← mkAppM ``Optic.Disjoint.unit_left #[n₂])
  if n₂.isAppOfArity ``Optic.Lens.unit 1 then
    return some (← mkAppM ``Optic.Disjoint.unit_right #[n₁])

  -- 4. `Lens.fst` / `Lens.snd`
  if n₁.isAppOfArity ``Optic.Lens.fst 2 && n₂.isAppOfArity ``Optic.Lens.snd 2 then
    return some (← mkAppOptM ``Optic.Disjoint.fst_snd #[some (n₁.getArg! 0), some (n₁.getArg! 1)])
  if n₁.isAppOfArity ``Optic.Lens.snd 2 && n₂.isAppOfArity ``Optic.Lens.fst 2 then
    let h ← mkAppOptM ``Optic.Disjoint.fst_snd #[some (n₁.getArg! 0), some (n₁.getArg! 1)]
    return some (← mkAppM ``Optic.Disjoint.symm #[h])

  -- 5. Product lenses (`×ₗ`)
  if n₁.isAppOfArity ``Optic.Lens.prod 5 then
    let a := n₁.getArg! 3
    let b := n₁.getArg! 4
    if let some h₁ ← proveDisjoint? a n₂ (fuel - 1) then
      if let some h₂ ← proveDisjoint? b n₂ (fuel - 1) then
        return some (← mkAppM ``Optic.Disjoint.prod_left #[h₁, h₂])
  if n₂.isAppOfArity ``Optic.Lens.prod 5 then
    let a := n₂.getArg! 3
    let b := n₂.getArg! 4
    if let some h₁ ← proveDisjoint? n₁ a (fuel - 1) then
      if let some h₂ ← proveDisjoint? n₁ b (fuel - 1) then
        return some (← mkAppM ``Optic.Disjoint.prod_right #[h₁, h₂])

  -- 6. Composition chain descent & diverging-prefix lift
  -- Because `Lens.comp` is definitionally associative, re-associating to `head ∘ₗ tail` is defeq.
  let chain₁ ← splitCompChain n₁
  let chain₂ ← splitCompChain n₂
  if chain₁.size >= 1 && chain₂.size >= 1 && (chain₁.size > 1 || chain₂.size > 1) then
    let h₁ := chain₁[0]!
    let h₂ := chain₂[0]!
    let t₁ := chain₁.extract 1 chain₁.size
    let t₂ := chain₂.extract 1 chain₂.size
    if ← withReducible (isDefEq h₁ h₂) then
      -- Shared prefix: only disjoint if BOTH have tails and the tails are disjoint
      if t₁.isEmpty || t₂.isEmpty then
        return none
      if let some _ ← synthLawfulLens? h₁ then
        let tail₁ ← mkCompChain t₁
        let tail₂ ← mkCompChain t₂
        if let some hTail ← proveDisjoint? tail₁ tail₂ (fuel - 1) then
          let prf ← mkAppM ``Optic.Disjoint.comp_same #[h₁, hTail]
          return some (← mkExpectedTypeHint prf goalTy)
    else
      -- Diverging outer heads: prove `Disjoint h₁ h₂` once and lift tails
      if let some hHeads ← proveDisjoint? h₁ h₂ (fuel - 1) then
        let prf? ← match t₁.isEmpty, t₂.isEmpty with
          | true, true => pure (some hHeads)
          | false, true =>
            if let some _ ← synthLawfulLens? h₁ then
              some <$> mkAppM ``Optic.Disjoint.comp_left #[← mkCompChain t₁, hHeads]
            else pure none
          | true, false =>
            if let some _ ← synthLawfulLens? h₂ then
              some <$> mkAppM ``Optic.Disjoint.comp_right #[← mkCompChain t₂, hHeads]
            else pure none
          | false, false =>
            if (← synthLawfulLens? h₁).isSome && (← synthLawfulLens? h₂).isSome then
              some <$> mkAppM ``Optic.Disjoint.comp #[← mkCompChain t₁, ← mkCompChain t₂, hHeads]
            else pure none
        if let some prf := prf? then
          return some (← mkExpectedTypeHint prf goalTy)

  -- 7. Distinct `make_lenses` fields on the same structure (O(1), no sub-struct unfolding)
  if let some prf ← proveDistinctStructFields? n₁ n₂ then
    return some (← mkExpectedTypeHint prf goalTy)

  -- 8. `Lens.atKey k₁` vs `Lens.atKey k₂`
  if n₁.isAppOfArity ``Optic.Lens.atKey 4 && n₂.isAppOfArity ``Optic.Lens.atKey 4 then
    let kTy := n₁.getArg! 0
    let vTy := n₁.getArg! 1
    let decInst := n₁.getArg! 2
    let k₁ := n₁.getArg! 3
    let k₂ := n₂.getArg! 3
    if let some hne ← proveNe? k₁ k₂ then
      let prf ← mkAppOptM ``Optic.Disjoint.atKey_of_ne
        #[some kTy, some vTy, some decInst, some k₁, some k₂, some hne]
      return some (← mkExpectedTypeHint prf goalTy)

  -- 9. Registered `@[lens_disjoint]` lemmas (direct and symmetric)
  let solveSub (subTy : Expr) : MetaM (Option Expr) := do
    let subTy := (← instantiateMVars subTy).consumeMData
    if subTy.isAppOfArity ``Optic.Disjoint 5 then
      return ← proveDisjoint? (subTy.getArg! 3) (subTy.getArg! 4) (fuel - 1)
    if subTy.isAppOfArity ``Ne 3 then
      return ← proveNe? (subTy.getArg! 1) (subTy.getArg! 2)
    for decl in (← getLCtx) do
      if decl.isImplementationDetail then continue
      if ← isDefEq decl.type subTy then return some decl.toExpr
    return none

  let symmGoalTy ← mkAppM ``Optic.Disjoint #[l₂, l₁]
  for thmName in lensDisjointExt.getState (← getEnv) do
    if let some prf ← tryApplyRegistered? thmName goalTy solveSub then
      return some prf
    if let some prf ← tryApplyRegistered? thmName symmGoalTy solveSub then
      return some (← mkAppM ``Optic.Disjoint.symm #[prf])

  -- 10. Structural fallback for ad-hoc user-defined lenses
  proveDisjointFallback? l₁ l₂

/-! ### Compositional `Independent` Prover & Derived-View Decomposition (`proveIndependent?`) -/

mutual

/-- Given `xVar : s` and `x' := l.set xVar v`, prove `body[xVar := x'] = body` by congruence-first
AST decomposition:
1. If `body` does not mention `xVar`, return `rfl`.
2. If `body` is a projection / lens path out of `xVar` (`lensPathFromProj?`), prove independence
   directly via `proveIndependent?`.
3. If `body` is an application `fn a₁ … aₙ`, try proving argument equalities by congruence first
   (avoiding unfolding `fn` if its arguments are already preserved!).
4. If congruence fails and `fn` is a user-defined derived view (non-recursor, non-constructor),
   unfold `fn` once and recurse! -/
private partial def proveViewBodyEq? (l xVar vVar x' : Expr) (body : Expr) (fuel : Nat) :
    MetaM (Option Expr) := do
  if fuel == 0 then return none
  let body := (← instantiateMVars body).consumeMData
  if !body.containsFVar xVar.fvarId! then
    return some (← mkEqRefl body)

  -- Direct projection / lens / map-lookup path from `xVar`
  if let some kLens ← lensPathFromProj? xVar body then
    let kLensWhnf ← whnfOptic kLens
    unless kLensWhnf.isAppOfArity ``Optic.Lens.id 1 do
      let kGetter ← mkAppM ``Optic.Lens.toGetter #[kLens]
      if let some hind ← proveIndependent? l kGetter (fuel - 1) then
        let prf := mkApp2 hind xVar vVar
        let lhs := body.replaceFVar xVar x'
        let expected ← mkEq lhs body
        if ← isDefEq (← inferType prf) expected then
          return some (← mkExpectedTypeHint prf expected)

  -- Function application: congruence-first, then unfold derived view on miss
  if body.isApp then
    let fn := body.getAppFn
    let args := body.getAppArgs
    if !fn.containsFVar xVar.fvarId! then
      let congrPrf? ← commitWhenSomeNoEx? do
        let mut acc ← mkEqRefl fn
        let mut curLhs := fn
        let mut curRhs := fn
        let mut allOk := true
        for arg in args do
          if !arg.containsFVar xVar.fvarId! then
            acc ← mkCongrFun acc arg
            curLhs := mkApp curLhs arg
            curRhs := mkApp curRhs arg
          else
            let some hArg ← proveViewBodyEq? l xVar vVar x' arg (fuel - 1)
              | allOk := false; break
            -- Check whether the function type is non-dependent at this argument
            let fnTy ← whnf (← inferType curLhs)
            if fnTy.isForall && !fnTy.bindingBody!.hasLooseBVars then
              acc ← mkCongr acc hArg
              curLhs := mkApp curLhs (arg.replaceFVar xVar x')
              curRhs := mkApp curRhs arg
            else
              allOk := false
              break
        if allOk then return some acc else return none
      if congrPrf?.isSome then
        return congrPrf?
      -- Congruence missed (an argument depends on a modified field): unfold derived view `fn`
      if fn.constName?.isSome then
        if let some body' ← unfoldDefinition? body then
          let body' := body'.headBeta
          if body' != body then
            if let some prf ← proveViewBodyEq? l xVar vVar x' body' (fuel - 1) then
              let expected ← mkEq (body.replaceFVar xVar x') body
              return some (← mkExpectedTypeHint prf expected)

  -- `let` expression: zeta-reduce
  if let .letE _ _ val b _ := body then
    let body' := b.instantiate1 val
    if let some prf ← proveViewBodyEq? l xVar vVar x' body' (fuel - 1) then
      let expected ← mkEq (body.replaceFVar xVar x') body
      return some (← mkExpectedTypeHint prf expected)

  -- Lambda expression: `funext`
  if let .lam n dom b bi := body then
    if !dom.containsFVar xVar.fvarId! then
      let prf? ← withLocalDecl n bi dom fun y => do
        let b' := b.instantiate1 y
        let some hb ← proveViewBodyEq? l xVar vVar x' b' (fuel - 1) | return none
        let lamPrf ← mkLambdaFVars #[y] hb
        some <$> mkAppM ``funext #[lamPrf]
      if prf?.isSome then return prf?

  -- Last resort at this subterm: definitional equality
  let lhs := body.replaceFVar xVar x'
  if ← isDefEq lhs body then
    return some (← mkEqRefl body)
  return none

/-- Recursively prove `Optic.Independent l g` compositionally across `Lens.unit`, `Lens.prod`,
`Getter.const`, `Getter.map`, `Getter.comp`, `Getter.prod`, `Lens.toGetter`, `@[lens_indep]`,
local hypotheses, and arbitrary derived views `Getter.of f`. -/
partial def proveIndependent? (l g : Expr) (fuel : Nat := 16) : MetaM (Option Expr) := do
  if fuel == 0 then return none
  let l ← instantiateMVars l
  let g ← instantiateMVars g
  let goalTy ← mkAppM ``Optic.Independent #[l, g]

  -- 1. Local context
  for decl in (← getLCtx) do
    if decl.isImplementationDetail then continue
    let dt := (← instantiateMVars decl.type).consumeMData
    if dt.isAppOfArity ``Optic.Independent 5 then
      if (← isDefEq (dt.getArg! 3) l) && (← isDefEq (dt.getArg! 4) g) then
        return some decl.toExpr

  let nl ← whnfOptic l
  let ng ← whnfOptic g

  -- 2. `Lens.unit` / `Getter.const`
  if nl.isAppOfArity ``Optic.Lens.unit 1 then
    return some (← mkAppM ``Optic.Independent.unit #[ng])
  if ng.isAppOfArity ``Optic.Getter.const 3 then
    return some (← mkAppM ``Optic.Independent.const #[nl, ng.getArg! 2])

  -- 3. `Lens.prod` on the left (`Independent (l₁ ×ₗ l₂) g`)
  if nl.isAppOfArity ``Optic.Lens.prod 5 then
    let l₁ := nl.getArg! 3
    let l₂ := nl.getArg! 4
    if let some h₁ ← proveIndependent? l₁ ng (fuel - 1) then
      if let some h₂ ← proveIndependent? l₂ ng (fuel - 1) then
        return some (← mkAppM ``Optic.Independent.prod_lens #[h₁, h₂])

  -- 4. `Lens.toGetter k`: delegate to `proveDisjoint?`
  if ng.isAppOfArity ``Optic.Lens.toGetter 3 then
    let k := ng.getArg! 2
    if let some _ ← synthLawfulLens? k then
      if let some hdisj ← proveDisjoint? nl k (fuel - 1) then
        let prf ← mkAppM ``Optic.Disjoint.independent_left #[hdisj]
        return some (← mkExpectedTypeHint prf goalTy)

  -- 5. `Iso.toGetter i`: delegate via `i.toLens`
  if ng.isAppOfArity ``Optic.Iso.toGetter 3 then
    let i := ng.getArg! 2
    let k ← mkAppM ``Optic.Iso.toLens #[i]
    if let some _ ← synthLawfulLens? k then
      if let some hdisj ← proveDisjoint? nl k (fuel - 1) then
        let prf ← mkAppM ``Optic.Disjoint.independent_left #[hdisj]
        return some (← mkExpectedTypeHint prf goalTy)

  -- 6. Structural getter combinators (`map`, `comp`, `prod`)
  if ng.isAppOfArity ``Optic.Getter.map 5 then
    let f := ng.getArg! 3
    let g₁ := ng.getArg! 4
    if let some h₁ ← proveIndependent? nl g₁ (fuel - 1) then
      return some (← mkAppM ``Optic.Independent.map #[f, h₁])

  if ng.isAppOfArity ``Optic.Getter.comp 5 then
    let g₁ := ng.getArg! 3
    let g₂ := ng.getArg! 4
    -- First: if `g₁` is already independent of `nl`, lift via `comp_getter`
    if let some h₁ ← proveIndependent? nl g₁ (fuel - 1) then
      return some (← mkAppM ``Optic.Independent.comp_getter #[g₂, h₁])
    -- Second: shared outer lens prefix (`outer ∘ₗ inner` vs `outer.toGetter ∘ᵍ g₂`)
    let g₁n ← whnfOptic g₁
    if g₁n.isAppOfArity ``Optic.Lens.toGetter 3 then
      let outerG := g₁n.getArg! 2
      let chain ← splitCompChain nl
      if chain.size > 1 && (← withReducible (isDefEq chain[0]! outerG)) then
        if let some _ ← synthLawfulLens? outerG then
          let innerL ← mkCompChain (chain.extract 1 chain.size)
          if let some hInner ← proveIndependent? innerL g₂ (fuel - 1) then
            let prf ← mkAppM ``Optic.Independent.comp_same #[outerG, hInner]
            return some (← mkExpectedTypeHint prf goalTy)

  if ng.isAppOfArity ``Optic.Getter.prod 5 then
    let g₁ := ng.getArg! 3
    let g₂ := ng.getArg! 4
    if let some h₁ ← proveIndependent? nl g₁ (fuel - 1) then
      if let some h₂ ← proveIndependent? nl g₂ (fuel - 1) then
        return some (← mkAppM ``Optic.Independent.prod #[h₁, h₂])

  -- 7. Registered `@[lens_indep]` lemmas
  let solveSub (subTy : Expr) : MetaM (Option Expr) := do
    let subTy := (← instantiateMVars subTy).consumeMData
    if subTy.isAppOfArity ``Optic.Independent 5 then
      return ← proveIndependent? (subTy.getArg! 3) (subTy.getArg! 4) (fuel - 1)
    if subTy.isAppOfArity ``Optic.Disjoint 5 then
      return ← proveDisjoint? (subTy.getArg! 3) (subTy.getArg! 4) (fuel - 1)
    if subTy.isAppOfArity ``Ne 3 then
      return ← proveNe? (subTy.getArg! 1) (subTy.getArg! 2)
    for decl in (← getLCtx) do
      if decl.isImplementationDetail then continue
      if ← isDefEq decl.type subTy then return some decl.toExpr
    return none

  for thmName in lensIndepExt.getState (← getEnv) do
    if let some prf ← tryApplyRegistered? thmName goalTy solveSub then
      return some prf

  -- 8. Derived views `Getter.of f` (named views, lambdas, struct projections)
  if ng.isAppOfArity ``Optic.Getter.of 3 then
    let f := ng.getArg! 2
    let lTy ← whnf (← inferType nl)
    if lTy.isAppOfArity ``Optic.Lens 2 then
      let sTy := lTy.getArg! 0
      let aTy := lTy.getArg! 1
      let viewPrf? ← withLocalDeclD `x sTy fun xVar =>
        withLocalDeclD `v aTy fun vVar => do
          let x' ← mkAppM ``Optic.Lens.set #[nl, xVar, vVar]
          let body := (mkApp f xVar).headBeta
          let some eqPrf ← proveViewBodyEq? nl xVar vVar x' body (fuel - 1) | return none
          let prf ← mkLambdaFVars #[xVar, vVar] eqPrf
          return some (← mkExpectedTypeHint prf goalTy)
      if viewPrf?.isSome then return viewPrf?

  -- 9. Fast definitional / cases fallback
  let mvar ← mkFreshExprMVar goalTy
  let ok ← commitWhen do
    try
      let (xs, g) ← mvar.mvarId!.introN 2
      let closedRfl ← commitWhen do
        try g.refl; return true catch _ => return false
      if closedRfl then return true
      let sgs ← g.cases xs[0]!
      for sg in sgs do
        sg.mvarId.refl
      return true
    catch _ =>
      return false
  if ok then
    return some (← instantiateMVars mvar)
  return none

end

/-! ### User-Facing Tactics (`lens_disjoint`, `lens_indep`) -/

/-- Discharge `Optic.Disjoint l₁ l₂`, `Optic.Independent l g`, or a preservation statement
`∀ s' s, ReflTransGen (Modifies l) s' s → g.get s' = g.get s` using path-aware compositional
reasoning (without unfolding untouched sub-structures). -/
elab "lens_disjoint" : tactic => withMainContext do
  let g ← getMainGoal
  let target := (← instantiateMVars (← g.getType)).consumeMData
  if target.isAppOfArity ``Optic.Disjoint 5 then
    let l₁ := target.getArg! 3
    let l₂ := target.getArg! 4
    let some prf ← proveDisjoint? l₁ l₂
      | throwError "lens_disjoint: failed to prove disjointness:{indentExpr target}"
    g.assign prf
  else if target.isAppOfArity ``Optic.Independent 5 then
    let l := target.getArg! 3
    let gt := target.getArg! 4
    let some prf ← proveIndependent? l gt
      | throwError "lens_disjoint: failed to prove independence:{indentExpr target}"
    g.assign prf
  else
    throwError "lens_disjoint: expected `Optic.Disjoint` or `Optic.Independent`, got:{indentExpr target}"

/-- Discharge `Optic.Independent l g` goals (compositional views, getters, products, `atKey`). -/
elab "lens_indep" : tactic => withMainContext do
  let g ← getMainGoal
  let target := (← instantiateMVars (← g.getType)).consumeMData
  unless target.isAppOfArity ``Optic.Independent 5 do
    throwError "lens_indep: expected `Optic.Independent`, got:{indentExpr target}"
  let l := target.getArg! 3
  let gt := target.getArg! 4
  let some prf ← proveIndependent? l gt
    | throwError "lens_indep: failed to prove independence:{indentExpr target}"
  g.assign prf

end Optic.Tactic

end
