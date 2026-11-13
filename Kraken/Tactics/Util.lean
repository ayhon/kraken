module

public import Kraken.Attribute
public import Kraken.BitVecArith
public import Kraken.Mem
public import Kraken.Separation
public import Kraken.SeparationMem
public import Kraken.ToBytes
public meta import Lean.Elab.Tactic
public meta import Lean.Meta.Tactic.Grind
public meta import Lean.Elab.Tactic.Omega

/-!
# Shared Tactic Utilities and Side-Goal Solvers

Common `MetaM` and `TacticM` helpers, goal-splitting and hypothesis-filtering utilities,
and fast arithmetic / `BitVec` side-goal solvers used across the Kraken tactic suite.
-/

public section

/-- Marker on loop-invariant conjuncts (`pc` and register frame) synthesized by
`kloop at "…" (writes/preserves := […])`, so `init`, `body`, and `kloop_next` can peel and
discharge them automatically without disturbing user-written invariant conjuncts. -/
@[expose] def Kraken.LoopAuto (P : Prop) : Prop := P

end

public meta section

open Lean Elab Tactic Meta

namespace Kraken.Tactic

initialize registerTraceClass `Kraken.sep

/-! ### General MetaM & TacticM Combinators -/

/-- Run `x` with `maxRecDepth` raised to at least `4096`. -/
def withKrakenRecDepth {α : Type} (x : TacticM α) : TacticM α :=
  withOptions (fun opts =>
    let cur := maxRecDepth.get opts
    if cur < 4096 then maxRecDepth.set opts 4096 else opts) x

/-- Check whether `t` is an application of an architecture's `Reg64s.CalleeSavedEq` predicate. -/
def isCalleeSavedEqType (t : Expr) : Bool :=
  match t.consumeMData.getAppFn'.constName? with
  | some n => (`Reg64s.CalleeSavedEq).isSuffixOf n
  | none => false

/-- Clear local `let` bindings, separation-logic hypotheses, and (optionally) `CalleeSavedEq`
hypotheses before invoking `grind` or `kaddr`. -/
def clearSepAndLets (mvarId : MVarId) (clearCS : Bool := true) : MetaM MVarId :=
  mvarId.withContext do
    let mut toClear : Array FVarId := #[]
    for localDecl? in (← getLCtx).decls do
      if let some localDecl := localDecl? then
        if localDecl.hasValue ||
           localDecl.type.getAppFn.isConstOf ``Std.ExtHashMap.sep ||
           localDecl.type.isAppOf ``Std.ExtHashMap ||
           (clearCS && isCalleeSavedEqType localDecl.type) then
          toClear := toClear.push localDecl.fvarId
    mvarId.tryClearMany toClear

/-- Unroll a literal `List` expression into its elements (after `whnfD` along the spine). -/
partial def literalListElems (l : Expr) : MetaM (Array Expr) := do
  let mut acc := #[]
  let mut cur ← whnfD l
  while cur.isAppOfArity ``List.cons 3 do
    acc := acc.push (cur.getArg! 1)
    cur ← whnfD (cur.getArg! 2)
  unless cur.isAppOfArity ``List.nil 1 do
    throwError "expected a literal list, got{indentExpr l}"
  return acc

/-- Split a goal into its conjunctive components (`And` chains and `Prop`-valued structures),
returning the leaf goals in order. -/
partial def splitConjGoals (g : MVarId) : TacticM (List MVarId) := g.withContext do
  if ← g.isAssigned then return []
  let t := (← instantiateMVars (← g.getType)).consumeMData
  if t.isAppOfArity ``And 2 then
    let gs ← g.apply (mkConst ``And.intro)
    gs.foldlM (fun acc g' => do return acc ++ (← splitConjGoals g')) []
  else if let some n := t.getAppFn.constName? then
    if n != ``Exists && isStructure (← getEnv) n && (← isProp t) then
      let gs ← g.constructor
      gs.foldlM (fun acc g' => do return acc ++ (← splitConjGoals g')) []
    else
      return [g]
  else
    return [g]

/-- Check whether any application head in `e` is one of `names`. -/
def mentionsConst (e : Expr) (names : List Name) : Bool :=
  (e.find? fun s =>
    match s.getAppFn.constName? with
    | some n => names.contains n
    | none => false).isSome

/-- Run `tac` on the current goal; succeed only if it closes all goals, otherwise roll back
(including on runtime exceptions such as `maxRecDepth`). -/
def tryClose (tac : TSyntax `tactic) : TacticM Bool := do
  let s ← saveState
  tryCatchRuntimeEx
    (do
      Tactic.withoutRecover (evalTactic tac)
      if (← getUnsolvedGoals).isEmpty then return true
      s.restore; return false)
    (fun _ => do s.restore; return false)

/-- Close `g` if it is a conjunction of context hypotheses, `True`, or reflexive equations;
otherwise leave the state untouched. -/
def tryCloseSimple (g : MVarId) : TacticM Bool := do
  let s ← saveState
  setGoals [g]
  let ok ← try
      evalTactic (← `(tactic| (try dsimp only)))
      if (← getUnsolvedGoals).isEmpty then pure true else
      let g ← getMainGoal
      let leaves ← splitConjGoals g
      let mut all := true
      for l in leaves do
        if ← l.isAssigned then continue
        setGoals [l]
        let closed ← do
          if ← tryClose (← `(tactic| assumption)) then pure true
          else if ← tryClose (← `(tactic| exact True.intro)) then pure true
          else tryClose (← `(tactic| with_reducible rfl))
        unless closed do all := false
      pure all
    catch _ => pure false
  if ok then return true
  s.restore
  return false

/-! ### Linear Byte-Length Arithmetic Solver -/

/-- Simp lemmas normalising byte-list lengths (`List.length_drop`, `Int.toBytes_length`, …). -/
def lengthSimpLemmas : List Name :=
  [``List.length_drop, ``List.length_take, ``List.length_append, ``List.length_replicate,
   ``List.length_cons, ``List.length_nil, ``List.length_map, ``List.length_reverse,
   ``Int.toBytes_length, ``Nat.toBytes_length, ``UInt8.toBytes_length, ``UInt16.toBytes_length,
   ``UInt32.toBytes_length, ``UInt64.toBytes_length]

/-- Add the lemmas `simp only` always includes (`eq_self`, `iff_self`) so goals reduced to
`a = a` are closed. -/
def simpOnlyBuiltinThms (s : SimpTheorems) : MetaM SimpTheorems := do
  let mut s := s
  for n in Lean.Elab.Tactic.simpOnlyBuiltins do
    s ← s.addConst n
  return s

/-- Check whether `t` is a linear-arithmetic proposition over `Nat`/`Int` (an (in)equality or
boolean combination of them) that `omega` can decide. -/
partial def isArithProp (t : Expr) : MetaM Bool := do
  let t := t.consumeMData
  if t.isAppOfArity ``And 2 then
    return (← isArithProp (t.getArg! 0)) && (← isArithProp (t.getArg! 1))
  if t.isAppOfArity ``Not 1 then return ← isArithProp (t.getArg! 0)
  let isNatInt (ty : Expr) : MetaM Bool := do
    let ty ← whnfR ty
    return ty.isConstOf ``Nat || ty.isConstOf ``Int
  if let some (ty, _, _) := t.eq? then return ← isNatInt ty
  if t.isAppOfArity ``LE.le 4 || t.isAppOfArity ``LT.lt 4 || t.isAppOfArity ``GE.ge 4 ||
      t.isAppOfArity ``GT.gt 4 || t.isAppOfArity ``Ne 3 then
    return ← isNatInt (t.getArg! 0)
  return false

private initialize lengthSimpTheoremsCache : IO.Ref (Option SimpTheorems) ← IO.mkRef none

private def getLengthSimpTheorems : MetaM SimpTheorems := do
  if let some thms ← lengthSimpTheoremsCache.get then
    return thms
  let thms ← lengthSimpLemmas.foldlM (fun (s : SimpTheorems) n => s.addConst n) {}
  let thms ← simpOnlyBuiltinThms thms
  lengthSimpTheoremsCache.set (some thms)
  return thms

/-- Close an arithmetic side goal (typically a byte-length condition such as
`(List.drop 8 bs).length = 8` or `k ≤ bs.length`) by normalising lengths with
`lengthSimpLemmas` and running `omega`. -/
def solveArithGoal (g : MVarId) : MetaM Bool := g.withContext do
  commitWhen do
    try
      let simpThms ← getLengthSimpTheorems
      let ctx ← Simp.mkContext {} (simpTheorems := #[simpThms]) (congrTheorems := ← getSimpCongrTheorems)
      let g ← (do
        let (r, _) ← simpGoal g ctx (simprocs := #[← Simp.getSimprocs])
        pure (r.map (·.2))) <|> pure (some g)
      let some g := g | return true
      let some g ← g.falseOrByContra | return true
      g.withContext do
        let hyps := (← getLocalHyps).toList
        Lean.Elab.Tactic.Omega.omega hyps g {}
      return true
    catch e =>
      trace[Kraken.sep] "solveArithGoal failed: {e.toMessageData}"
      return false

/-- Return `some true` if `prop` holds by `solveArithGoal`, `some false` if its negation does,
or `none` otherwise. -/
def decideArithProp (prop : Expr) : MetaM (Option Bool) := withoutModifyingState do
  let g ← mkFreshExprMVar prop
  if ← solveArithGoal g.mvarId! then return some true
  let gNot ← mkFreshExprMVar (mkNot prop)
  if ← solveArithGoal gNot.mvarId! then return some false
  return none

/-! ### Fast `BitVec` Address Normalization -/

private initialize bitVecEqSimpTheoremsCache : IO.Ref (Option SimpTheorems) ← IO.mkRef none

private def getBitVecEqSimpTheorems : MetaM SimpTheorems := do
  if let some thms ← bitVecEqSimpTheoremsCache.get then
    return thms
  let thms ← ([``BitVec.add_assoc] : List Name).foldlM (fun (s : SimpTheorems) n => s.addConst n) {}
  let thms ← thms.addConst ``BitVec.ofNat_add (inv := true)
  let thms ← simpOnlyBuiltinThms thms
  bitVecEqSimpTheoremsCache.set (some thms)
  return thms

/-- Normalise a goal `lhs = rhs` of `BitVec` sums: right-associate and fold literal offsets
(`a + 16#64 + 8#64 ↦ a + 24#64`). Returns `none` if the goal was closed, else the new goal. -/
def normBitVecEqGoal (g : MVarId) : MetaM (Option MVarId) := g.withContext do
  let thms ← getBitVecEqSimpTheorems
  let ctx ← Simp.mkContext {} (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  let (r, _) ← simpGoal g ctx (simprocs := #[← Simp.getSimprocs])
  return r.map (·.2)

/-- Prove an equality of `BitVec` sums by right-associating and folding literals. -/
def proveBitVecEqByNorm (g : MVarId) : MetaM Bool := g.withContext do
  commitWhen do
    try
      return (← normBitVecEqGoal g).isNone
    catch _ => return false

/-- `base + offset` decomposition of a normalised `BitVec` sum (`offset := 0` if absent). -/
def bvBaseOffset? (e : Expr) : Option (Expr × Nat) :=
  if e.isAppOfArity ``HAdd.hAdd 6 then
    let b := e.getArg! 4
    let o := e.getArg! 5
    if o.isAppOfArity ``BitVec.ofNat 2 then
      match (o.getArg! 1).nat? with
      | some n => some (b, n)
      | none => some (e, 0)
    else some (e, 0)
  else some (e, 0)

/-- Decide an equality of `BitVec 64` address sums: `some true` if it holds after normalisation,
`some false` if both sides share a base with different literal offsets, `none` otherwise. -/
def decideBitVecAddEq (prop : Expr) : MetaM (Option Bool) := withoutModifyingState do
  let some (ty, _, _) := prop.consumeMData.eq? | return none
  unless (← whnfR ty).isAppOfArity ``BitVec 1 do return none
  let g ← mkFreshExprMVar prop
  try
    let some g' ← normBitVecEqGoal g.mvarId! | return some true
    let t ← instantiateMVars (← g'.getType)
    let some (_, lhs, rhs) := t.consumeMData.eq? | return none
    let some (b₁, o₁) := bvBaseOffset? lhs | return none
    let some (b₂, o₂) := bvBaseOffset? rhs | return none
    if b₁ == b₂ && o₁ < 2 ^ 64 && o₂ < 2 ^ 64 && o₁ != o₂ then return some false
    return none
  catch _ => return none

/-! ### Propositional Side-Goal Solver -/

/-- Prove a propositional side goal using fast `BitVec` address normalization, `omega` on linear
length arithmetic, or `grind` as a fallback. -/
def provePropGoal (prop : Expr) : MetaM (Option Expr) :=
  commitWhenSomeNoEx? do
    let prop ← instantiateMVars prop
    -- Cheap path: address equalities of `BitVec` sums.
    if let some (ty, _, _) := prop.consumeMData.eq? then
      if (← whnfR ty).isAppOfArity ``BitVec 1 then
        let goal ← mkFreshExprMVar prop
        let normRes? ← try some <$> normBitVecEqGoal goal.mvarId! catch _ => pure none
        if let some optG := normRes? then
          match optG with
          | none =>
            trace[Kraken.sep] "provePropGoal by BitVec normalisation: {prop}"
            return some (← instantiateMVars goal)
          | some g' =>
            let t ← instantiateMVars (← g'.getType)
            if let some (_, lhs, rhs) := t.consumeMData.eq? then
              if let (some (b₁, o₁), some (b₂, o₂)) := (bvBaseOffset? lhs, bvBaseOffset? rhs) then
                if b₁ == b₂ && o₁ < 2 ^ 64 && o₂ < 2 ^ 64 && o₁ != o₂ then
                  trace[Kraken.sep] "provePropGoal refuted by BitVec normalisation: {prop}"
                  return none
    -- Cheap path: linear length arithmetic (`omega`, with negation check to skip `grind`).
    if ← isArithProp prop then
      let goal ← mkFreshExprMVar prop
      if ← solveArithGoal goal.mvarId! then
        trace[Kraken.sep] "provePropGoal by omega: {prop}"
        return some (← instantiateMVars goal)
      let gNot ← mkFreshExprMVar (mkNot prop)
      if ← solveArithGoal gNot.mvarId! then
        trace[Kraken.sep] "provePropGoal refuted by omega: {prop}"
        return none
    trace[Kraken.sep] "provePropGoal by grind: {prop}"
    let hasBytesInProp :=
      (prop.find? (fun e => e.isConstOf ``Int.ofBytes || e.isConstOf ``Int.toBytes)).isSome
    let goal ← mkFreshExprMVar prop
    let mut toClear : Array FVarId := #[]
    for localDecl? in (← getLCtx).decls do
      if let some localDecl := localDecl? then
        if localDecl.hasValue ||
           (localDecl.type.find? (·.isConstOf ``Std.ExtHashMap)).isSome ||
           isCalleeSavedEqType localDecl.type ||
           (!hasBytesInProp && (localDecl.type.find? (fun e => e.isConstOf ``Int.ofBytes || e.isConstOf ``Int.toBytes)).isSome) then
          toClear := toClear.push localDecl.fvarId
    let goalId ← goal.mvarId!.tryClearMany toClear
    let params ← Lean.Meta.Grind.mkDefaultParams {}
    let res ← Lean.Meta.Grind.main goalId params
    if res.hasFailed then return none
    unless ← goal.mvarId!.isAssigned do return none
    return some (← instantiateMVars goal)

/-- Prove `lhs = rhs` when their types are definitionally equal. -/
def provePropEq (lhs rhs : Expr) : MetaM (Option Expr) := do
  unless ← commitWhen (isDefEq (← inferType lhs) (← inferType rhs)) do return none
  provePropGoal (← mkEq lhs rhs)

end Kraken.Tactic
end
