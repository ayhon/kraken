module

public import Kraken.Tactics.Util

/-!
# Symbolic Residue Normalization and Branch-Condition Simplification

Normal-form theorem sets, ground arithmetic simprocs, atomic `let`-inlining, stuck-matcher
reduction, and `@[kcond]` branch-condition simplification used by `kstep` and `kfinish`.
-/

public section

attribute [grind =]
  BitVec.ofInt_natCast
  BitVec.ofNat_add
  Int.natCast_shiftLeft
  List.length_append
  List.length_take
  List.length_drop
  List.drop_drop
  List.take_of_length_le
  List.take_replicate
  List.drop_replicate
  UInt64.toBitVec_add

attribute [ksimp]
  Int64.ofBitVec_toBitVec
  BitVec.add_zero
  BitVec.zero_add
  BitVec.ofInt_add
  BitVec.ofInt_mul
  BitVec.ofInt_natCast
  BitVec.ofInt_ofNat
  BitVec.ofInt_toInt
  BitVec.ofNat_eq_ofNat
  BitVec.ofNat_add
  BitVec.ofNat_mul
  BitVec.ofNat_toNat
  BitVec.ofNat_uInt64ToNat
  BitVec.setWidth_eq
  BitVec.shiftLeft_zero
  BitVec.zero_shiftLeft
  BitVec.zero_or
  BitVec.or_zero
  BitVec.xor_self
  BitVec.ofInt_ofBytes_toBytes_8
  BitVec.ofInt_ofBytes_toBytes_16
  BitVec.ofInt_ofBytes_toBytes_32
  BitVec.ofInt_ofBytes_toBytes_64
  BitVec.ofInt_ofBytes_uInt8ToBytes
  BitVec.ofInt_ofBytes_uInt16ToBytes
  BitVec.ofInt_ofBytes_uInt32ToBytes
  BitVec.ofInt_ofBytes_uInt64ToBytes
  Int.add_zero
  Int.natCast_shiftLeft
  Int.toBytes_length
  Int.toBytes_zero
  Int64.toInt_neg
  Nat.shiftRight_zero
  Nat.sub_zero
  Nat.toBytes_length
  UInt8.toBytes_length
  UInt16.toBytes_length
  UInt32.toBytes_length
  UInt64.toBytes_length
  UInt64.ofBitVec_add
  UInt64.ofBitVec_ofNat
  UInt64.ofBitVec_sub
  UInt64.ofBitVec_toBitVec
  UInt64.sub_add_cancel
  UInt64.toBitVec_add
  UInt64.toBitVec_ofNat
  UInt64.toBitVec_sub
  UInt64.toNat_toBitVec

end

public meta section

open Lean Elab Tactic Meta

namespace Kraken.Tactic

/-! ### Stuck-Matcher Reduction and `let` Inlining -/

private def getStructureCtor? (major : Expr) : MetaM Name := do
  let ty ← whnfD (← inferType major)
  let .const tyName _ := ty.getAppFn | return .anonymous
  let some _ := getStructureInfo? (← getEnv) tyName | return .anonymous
  return (getStructureCtor (← getEnv) tyName).name

/-- Reduce `match` applications and structure projections whose discriminant is a constructor
application, everywhere in `e` (including implicit and instance arguments, which `Sym`
simplifiers do not visit). The result is definitionally equal to `e`. -/
def reduceStuckMatchers (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun e => do
    if let .const fn _ := e.getAppFn then
      if (← getMatcherInfo? fn).isSome then
        if let .reduced e' ← reduceMatcher? e then return .visit e'
      else if e.isApp then
        if let some info ← getProjectionFnInfo? fn then
          if !info.fromClass && e.getAppNumArgs > info.numParams then
            let major := e.getArg! info.numParams
            if (← whnfCore major).isAppOf (← getStructureCtor? major) then
              if let some e' ← Meta.unfoldDefinition? e then
                let e'' ← whnfCore e'
                unless e''.isProj do return .visit e''
    else if e.isProj then
      let e' ← whnfCore e
      unless e'.isProj do return .visit e'
    return .continue)

/-- Number of nodes of `e`, saturating at `cap + 1`; binders count as exceeding the cap. -/
private def exprSizeCapped (e : Expr) (cap : Nat) : Nat :=
  go e cap
where
  go (e : Expr) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => cap + 1
    | fuel + 1 =>
      match e with
      | .app f a => go f fuel + go a fuel
      | .mdata _ e => go e fuel
      | .proj _ _ e => 1 + go e fuel
      | .lam .. | .forallE .. | .letE .. => cap + 1
      | _ => 1

/-- Check whether `e` is an atomic value worth inlining wherever its `let` is referenced:
a literal, a local variable, a closed term of at most `maxSize` nodes (an immediate such as
`BitVec.ofInt 64 1`), or a structure projection of a local variable (such as `X4.toBitVec`). -/
def isAtomicValue (e : Expr) (maxSize : Nat := 8) : MetaM Bool := do
  if e.isFVar || e.nat?.isSome || e.rawNatLit?.isSome then return true
  if e.hasMVar then return false
  if !e.hasFVar then return exprSizeCapped e maxSize ≤ maxSize
  if let .const fn _ := e.getAppFn then
    if let some info ← getProjectionFnInfo? fn then
      if !info.fromClass && e.getAppNumArgs == info.numParams + 1 then
        return (e.getArg! info.numParams).isFVar
  return false

/-- Replace `let`-bound local variables whose values satisfy `isAtomicValue` by their values so
that instruction residues become self-contained and their ground conditions and shift amounts
can be decided and folded. The result is definitionally equal to `e` (zeta-delta). -/
partial def inlineAtomicLets (e : Expr) : MetaM Expr := do
  let lctx ← getLCtx
  let mut subst : Std.HashMap FVarId Expr := {}
  for fvarId in (collectFVars {} e).fvarIds do
    if let some (.ldecl (value := v) ..) := lctx.find? fvarId then
      let v' ← inlineAtomicLets v
      if ← isAtomicValue v' then
        subst := subst.insert fvarId v'
  if subst.isEmpty then return e
  return e.replace fun
    | .fvar id => subst[id]?
    | _ => none

/-- Check whether `ty` is a machine-word-like type (`BitVec _`, `UInt*`, `Int*`, `Nat`, `Int`,
`Bool`) whose `let`-bound values should be normalised eagerly. -/
def isWordType (ty : Expr) : MetaM Bool := do
  let ty ← whnfR ty
  if ty.isAppOf ``BitVec then return true
  if let .const n _ := ty.getAppFn then
    return [``UInt64, ``UInt32, ``UInt16, ``UInt8, ``Int64, ``Int32, ``Int16, ``Int8, ``Nat, ``Int,
      ``Bool].contains n
  return false

/-! ### Symbolic State Normal Form -/

/-- Lemmas of the `BitVec`/`UInt64` normal form in which `kstep` leaves its symbolic state
(also used by `kfinish`). -/
def normalFormLemmas : List Name :=
  [``BitVec.shiftLeft_zero, ``BitVec.zero_shiftLeft, ``BitVec.add_zero, ``BitVec.zero_add,
   ``BitVec.or_zero, ``BitVec.zero_or, ``BitVec.xor_self, ``BitVec.setWidth_eq,
   ``UInt64.toNat_toBitVec, ``UInt64.toBitVec_ofBitVec, ``UInt64.ofBitVec_toBitVec,
   ``Int64.ofBitVec_toBitVec, ``Nat.sub_zero, ``Nat.add_zero, ``Nat.zero_add,
   ``Nat.shiftRight_zero, ``UInt64.bitVecOfNat_toNat, ``UInt32.bitVecOfNat_toNat,
   ``BitVec.ofNat_toNat,
   ``ite_true, ``ite_false, ``dite_true, ``dite_false,
   ``BitVec.setWidth_extractLsb'_ushiftRight]

private def natGroundHeads : List Name :=
  [``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``HMod.hMod, ``HPow.hPow,
   ``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.div, ``Nat.mod, ``Nat.pow, ``Nat.succ]

/-- Fold closed `Nat` arithmetic on literals (`64 - 1`, `63 + 1`) into a raw literal matching
the convention of `Sym`'s ground evaluator. -/
def reduceNatGround : Simp.Simproc := fun e => do
  let .const fn _ := e.getAppFn | return .continue
  unless natGroundHeads.contains fn do return .continue
  if e.hasFVar || e.hasMVar then return .continue
  let some n ← (Meta.evalNat e).run | return .continue
  return .done { expr := mkRawNatLit n }

/-- Fold a closed `BitVec.ofInt w i` into the raw literal `BitVec.ofNat w n`. -/
def reduceBitVecOfIntGround : Simp.Simproc := fun e => do
  let_expr BitVec.ofInt w i := e | return .continue
  if e.hasFVar || e.hasMVar then return .continue
  let some w ← (Meta.evalNat w).run | return .continue
  let some i ← getIntValue? i | return .continue
  let n := (i % (2 ^ w : Nat)).toNat
  return .done { expr := mkApp2 (mkConst ``BitVec.ofNat) (mkRawNatLit w) (mkRawNatLit n) }

/-- Fold closed `BitVec` modulo (`a % b`) where `a` or `b` may contain raw `Nat` literals from
`Sym`'s `evalGround`. -/
def reduceBitVecModGround : Simp.Simproc := fun e => do
  unless e.isAppOfArity ``HMod.hMod 6 || e.isAppOfArity ``BitVec.umod 3 do return .continue
  if e.hasFVar || e.hasMVar then return .continue
  let args := e.getAppArgs
  let a := args[args.size - 2]!
  let b := args[args.size - 1]!
  let some ⟨wa, bva⟩ ← getBitVecValue? a | return .continue
  let some ⟨wb, bvb⟩ ← getBitVecValue? b | return .continue
  if h : wa = wb then
    let res := bva % (h ▸ bvb)
    return .done { expr := toExpr res }
  return .continue

private initialize normalFormSimpTheoremsCache : IO.Ref (Option SimpTheorems) ← IO.mkRef none

private def getNormalFormSimpTheorems : MetaM SimpTheorems := do
  if let some thms ← normalFormSimpTheoremsCache.get then
    return thms
  let thms ← normalFormLemmas.foldlM (fun (s : SimpTheorems) n => do
    if (← getEnv).contains n then s.addConst n else pure s) {}
  normalFormSimpTheoremsCache.set (some thms)
  return thms

/-- Bring a term into normal form with the standard simplifier, deciding closed conditions and
folding closed `Nat` and `BitVec.ofInt` literals. Returns the simplified term and equality proof
if anything changed. -/
def simpNormalForm (e : Expr) : MetaM (Option (Expr × Expr)) := do
  tryCatchRuntimeEx
    (do
      let thms ← getNormalFormSimpTheorems
      let ctx ← Simp.mkContext { decide := true } (simpTheorems := #[thms])
        (congrTheorems := ← getSimpCongrTheorems)
      let methods := Simp.mkDefaultMethodsCore #[]
      let methods := { methods with
        post := fun e => do
          match ← reduceNatGround e with
          | .done r => return .done r
          | _ =>
            match ← reduceBitVecOfIntGround e with
            | .done r => return .done r
            | _ => methods.post e }
      let (r, _) ← Simp.main e ctx (methods := methods)
      if r.expr == e then return none
      let prf ← r.getProof
      return some (r.expr, prf))
    (fun _ => return none)

/-! ### Branch-Condition Lookup and `@[kcond]` Simplification -/

/-- Find a hypothesis proving `prop` up to definitional equality (including `let` bindings), or,
for `prop = ¬ (b = true)` / `¬ (b = false)`, a hypothesis `b' = false` / `b' = true` with `b ≡ b'`. -/
def assumptionModBool (prop : Expr) : MetaM (Option Expr) :=
  withConfig (fun c => { c with zetaDelta := true }) do
  withOptions (fun o => maxRecDepth.set o 256) do
  let prop ← instantiateMVars prop
  let isBoolEq (t : Expr) : Option (Expr × Expr) :=
    match t.consumeMData.eq? with
    | some (ty, lhs, rhs) => if ty.isConstOf ``Bool then some (lhs, rhs) else none
    | none => none
  let negated? : Option (Expr × Bool) :=
    match prop.consumeMData.not? with
    | some inner =>
      match isBoolEq inner with
      | some (b, v) =>
        if v.isConstOf ``Bool.true then some (b, true)
        else if v.isConstOf ``Bool.false then some (b, false) else none
      | none => none
    | none => none
  let defEq (a b : Expr) : MetaM Bool :=
    tryCatchRuntimeEx (withReducibleAndInstances (isDefEq a b) <||> isDefEq a b) (fun _ => pure false)
  let propStripped := prop.consumeMData
  let propHead := propStripped.getAppFn
  let propEqTy? := propStripped.eq?.map (·.1)
  for decl in (← getLCtx) do
    if decl.isImplementationDetail || decl.hasValue then continue
    let t ← instantiateMVars decl.type
    if t.hasExprMVar then continue
    let tStripped := t.consumeMData
    if tStripped.getAppFn == propHead then
      let sameEqTy ← match propEqTy?, tStripped.eq? with
        | some ty₁, some (ty₂, _, _) =>
          if ty₁ == ty₂ then pure true else withReducible (isDefEq ty₁ ty₂)
        | _, _ => pure true
      if sameEqTy then
        if ← defEq t prop then
          return some decl.toExpr
    if let some (b, v) := negated? then
      if let some (b', v') := isBoolEq t then
        if v && v'.isConstOf ``Bool.false && (← defEq b b') then
          return some (← mkExpectedTypeHint (← mkAppM ``ne_true_of_eq_false #[decl.toExpr]) prop)
        if !v && v'.isConstOf ``Bool.true && (← defEq b b') then
          return some (← mkExpectedTypeHint (← mkAppM ``ne_false_of_eq_true #[decl.toExpr]) prop)
  return none

inductive SimpWithHypsResult where
  | closed
  | refuted
  | goal (g : MVarId)

private initialize simpWithHypsBaseCache : IO.Ref (Option SimpTheorems) ← IO.mkRef none

private def getSimpWithHypsBaseTheorems : MetaM SimpTheorems := do
  if let some thms ← simpWithHypsBaseCache.get then
    return thms
  let mut thms : SimpTheorems := {}
  for n in [``bne_self_eq_false, ``beq_self_eq_true, ``Bool.false_eq_true, ``Bool.true_eq_false,
      ``Bool.not_false, ``Bool.not_true, ``decide_eq_true_eq, ``bne_iff_ne, ``beq_iff_eq,
      ``ne_eq, ``not_true_eq_false, ``not_false_eq_true,
      ``Bool.not_eq_true', ``decide_eq_false_iff_not, ``Bool.and_eq_true, ``Bool.or_eq_true,
      ``Nat.not_le, ``Nat.not_lt, ``Int.not_le, ``Int.not_lt,
      ``UInt64.toNat_toBitVec, ``UInt64.toBitVec_ofBitVec,
      ``BitVec.add_umod_16_right, ``BitVec.add_umod_16_left] do
    if (← getEnv).contains n then thms ← thms.addConst n
  thms ← simpOnlyBuiltinThms thms
  simpWithHypsBaseCache.set (some thms)
  return thms

/-- Simplify the goal using equational hypotheses in the context as rewrite rules (plus `Bool`,
`decide`, and `@[kcond]` flag projections). Reports whether the goal was closed, reduced to
`False`, or replaced by a simplified goal. -/
def simpWithHyps (g : MVarId) : MetaM SimpWithHypsResult := g.withContext do
  tryCatchRuntimeEx (do
    let mut thms ← getSimpWithHypsBaseTheorems
    for decl in (← getLCtx) do
      if decl.isImplementationDetail || decl.hasValue then continue
      let t ← instantiateMVars decl.type
      if t.hasExprMVar then continue
      if t.consumeMData.isAppOfArity ``Eq 3 || t.consumeMData.isAppOfArity ``Ne 3 ||
          t.consumeMData.isAppOfArity ``Not 1 then
        thms ← thms.add (.fvar decl.fvarId) #[] decl.toExpr
    let congrThms ← getSimpCongrTheorems
    let baseMethods := Simp.mkDefaultMethodsCore #[← Simp.getSimprocs]
    let methods := { baseMethods with
      post := fun e => do
        match ← reduceBitVecModGround e with
        | .done r => return .done r
        | _ => baseMethods.post e }
    let tgt ← instantiateMVars (← g.getType)
    -- Pass 1: rewrite with context hypotheses before unfolding `@[kcond]` flag definitions so
    -- compound carry/borrow hypotheses match before inner limbs expand into `decide (… ≤ …)`.
    let ctx1 ← Simp.mkContext { decide := true, zetaDelta := true } (simpTheorems := #[thms])
      (congrTheorems := congrThms)
    let (r1, _) ← Simp.main tgt ctx1 (methods := methods)
    if r1.expr.consumeMData.isConstOf ``True then
      g.assign (← mkOfEqTrue (← r1.getProof))
      return .closed
    else if r1.expr.consumeMData.isConstOf ``False then
      return .refuted
    -- Pass 2: unfold flag projections and the compare idiom (`@[kcond]`).
    let kcond ← kcondExt.getTheorems
    let ctx2 ← Simp.mkContext { decide := true, zetaDelta := true } (simpTheorems := #[thms, kcond])
      (congrTheorems := congrThms)
    let (r, _) ← Simp.main tgt ctx2 (methods := methods)
    if r.expr.consumeMData.isConstOf ``True then
      g.assign (← mkOfEqTrue (← r.getProof))
      return .closed
    else if r.expr.consumeMData.isConstOf ``False then
      return .refuted
    else if r.expr != tgt then
      let g' ← g.replaceTargetEq r.expr (← r.getProof)
      return .goal g'
    else
      return .goal g)
    (fun _ => return .goal g)

end Kraken.Tactic
end
