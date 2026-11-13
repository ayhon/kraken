module

public import Kraken.OmniSemantics
public import Kraken.Tactics.Addr

/-!
# Program Prologue, Trace Witness Unification, and Goal Termination

Tactics for setting up straight-line and sliced execution goals (`kprologue`, `kintro`,
`kpack_secrets`) and finishing stepped `Eventually` / `TracedEventually` goals (`kdone`).
-/

public meta section

open Lean Meta Elab Tactic Kraken Kraken.Tactic

/-! ### The `kprologue` Tactic -/

/-- Set up a straight-line proof for `p` (optionally from `at <idx|"label">`, running `take <n>`
directives or `to <idx|"label">`, and destructuring `with s` where `status` and `dmem` are named
`flags` and `mem`). -/
syntax (name := kprologue) "kprologue" ident ("at" term)? ("take" term)? ("to" term)? ("with" ident)? : tactic

private def kprologueBinderName (field : Lean.Name) : Lean.Name :=
  if field == `status then `flags
  else if field == `dmem then `mem
  else field

private partial def mkAndSplitPat (e : Expr) : TacticM (TSyntax `rcasesPat) := do
  let e := e.consumeMData
  if e.isAppOfArity ``And 2 then
    let p1 ← mkAndSplitPat (e.getArg! 0)
    let p2 ← mkAndSplitPat (e.getArg! 1)
    `(rcasesPat| ⟨$p1, $p2⟩)
  else if e.isConstOf ``True then
    `(rcasesPat| -)
  else
    `(rcasesPat| _)

private partial def bodyIsSpec (e : Expr) : Bool :=
  match e.consumeMData with
  | .forallE _ _ b _ => bodyIsSpec b
  | e => e.getAppFn'.constName? == some ``Kraken.Executable.Spec ||
         e.getAppFn'.constName? == some ``Kraken.Executable.ExecSpec

/-- Elaborate the destructuring pattern `⟨⟨r1, …⟩, flags, mem⟩` for `s : MachineData`, checking
for duplicate field names and local context shadowing. -/
private def mkStateDestructPat (s : Ident) : TacticM (TSyntax `rcasesPat) := do
  let env ← getEnv
  let state ← Term.elabTerm s none
  let stateType ← whnf (← inferType state)
  let some stateName := stateType.getAppFn.constName?
    | throwErrorAt s "kprologue: expected a state with a structure type"
  let some _ := getStructureInfo? env stateName
    | throwErrorAt s "kprologue: `{stateName}` is not a structure"

  let stateFields := getStructureFields env stateName
  let some regsInfo := getFieldInfo? env stateName `regs
    | throwErrorAt s "kprologue: `{stateName}` has no `regs` field"
  let regs ← mkAppM regsInfo.projFn #[state]
  let regsType ← whnf (← inferType regs)
  let some regsName := regsType.getAppFn.constName?
    | throwErrorAt s "kprologue: `{stateName}.regs` does not have a structure type"
  let some _ := getStructureInfo? env regsName
    | throwErrorAt s "kprologue: `{stateName}.regs` is not a structure"

  let regFields := getStructureFields env regsName
  let stateBinderNames := (stateFields.filter (· != `regs)).map kprologueBinderName
  let binderNames := regFields ++ stateBinderNames

  let mut seen : NameSet := {}
  let mut duplicateNames := #[]
  for name in binderNames do
    if seen.contains name then
      unless duplicateNames.contains name do
        duplicateNames := duplicateNames.push name
    else
      seen := seen.insert name
  unless duplicateNames.isEmpty do
    let names := String.intercalate ", " (duplicateNames.toList.map (·.toString))
    throwErrorAt s "kprologue: duplicate local names: {names}"

  let lctx ← getLCtx
  let collisions := binderNames.filter fun name => (lctx.findFromUserName? name).isSome
  unless collisions.isEmpty do
    let names := String.intercalate ", " (collisions.toList.map (·.toString))
    throwErrorAt s "kprologue: refusing to shadow existing locals: {names}"

  let regPats ← regFields.mapM fun field => do
    let id := mkIdentFrom s field
    `(rcasesPat| $id:ident)
  let regsPat ← `(rcasesPat| ⟨$[$regPats],*⟩)
  let statePats ← stateFields.mapM fun field =>
    if field == `regs then
      pure regsPat
    else do
      let id := mkIdentFrom s (kprologueBinderName field)
      `(rcasesPat| $id:ident)
  `(rcasesPat| ⟨$[$statePats],*⟩)

elab_rules : tactic
  | `(tactic| kprologue $p:ident $[at $kRaw?]? $[take $nRaw?]? $[to $toRaw?]? $[with $s?]?) => withKrakenRecDepth <| withMainContext do
      let targetInit := (← instantiateMVars (← getMainTarget)).consumeMData
      if targetInit.getAppFn'.constName? == some ``CtEventually then
        evalTactic (← `(tactic| unfold CtEventually))
      let targetEx := (← instantiateMVars (← getMainTarget)).consumeMData
      if targetEx.getAppFn'.constName? == some ``Exists then
        evalTactic (← `(tactic| (refine ⟨?_, ?_⟩; rotate_left)))
      while (← instantiateMVars (← getMainTarget)).consumeMData.headBeta.isForall &&
            bodyIsSpec (← instantiateMVars (← getMainTarget)).consumeMData.headBeta do
        let cur := (← instantiateMVars (← getMainTarget)).consumeMData.headBeta
        let id := mkIdent cur.bindingName!
        evalTactic (← `(tactic| intro $id:ident))
      let target0 := (← instantiateMVars (← getMainTarget)).consumeMData.headBeta
      if target0.getAppFn'.constName? == some ``Kraken.Executable.Spec ||
         target0.getAppFn'.constName? == some ``Kraken.Executable.ExecSpec then
        evalTactic (← `(tactic| dsimp only [Kraken.Executable.Spec, Kraken.Executable.ExecSpec]))
      let target1 := (← instantiateMVars (← getMainTarget)).consumeMData.headBeta
      if let .forallE _ reqType _ _ := target1 then
        let pat ← mkAndSplitPat reqType
        evalTactic (← `(tactic| rintro $pat:rcasesPat))
      evalTactic (← `(tactic| (try dsimp only [Kraken.Executable.startAddr_apply])))
      withMainContext do
      let curTarget := (← instantiateMVars (← getMainTarget)).consumeMData
      let isTraced := curTarget.getAppFn'.constName? == some ``TracedEventually
      let isTracedAccum := curTarget.isAppOfArity ``Eventually 4 &&
        (curTarget.getArg! 1).consumeMData.getAppFn'.constName? == some ``step1Traced
      let sliceThm := mkIdent (if isTraced then ``step1_cps_slice_traced else if isTracedAccum then ``step1_cps_slice_accum else ``step1_cps_slice)
      let atThm := mkIdent (if isTraced then ``step1_cps_at_traced else if isTracedAccum then ``step1_cps_at_accum else ``step1_cps_at)
      let cpsThm := mkIdent (if isTraced then ``step1_cps_traced else ``step1_cps)
      let (k?, startIdx?) ← match kRaw? with
        | some kRaw =>
          let (kTerm, idx?) ← resolveDirectivePos p kRaw
          pure (some kTerm, idx?)
        | none => pure (none, some 0)
      let n? ← match nRaw?, toRaw? with
        | some nRaw, none => pure (some nRaw)
        | none, some toRaw =>
          let (_, endIdx?) ← resolveDirectivePos p toRaw
          let (some startIdx, some endIdx) := (startIdx?, endIdx?)
            | throwErrorAt toRaw "kprologue: `to` requires statically known start and end positions"
          if endIdx < startIdx then
            throwErrorAt toRaw "kprologue: target position ({endIdx}) precedes start position ({startIdx})"
          pure (some (Syntax.mkNumLit (toString (endIdx - startIdx))))
        | none, none => pure none
        | some _, some toRaw => throwErrorAt toRaw "kprologue: cannot specify both `take` and `to`"
      let sliceConv ← `(tactic|
        conv =>
          arg 2
          rw [Kraken.Executable.program_apply_slice]
          arg 1
          (try delta $p)
          simp only [List.mapIdx_cons, List.mapIdx_nil,
                     List.drop_succ_cons, List.drop_zero, List.drop_nil,
                     List.take_succ_cons, List.take_zero, List.take_nil,
                     Nat.add_zero, Nat.zero_add, Nat.reduceAdd])
      let dropConv ← `(tactic|
        conv =>
          arg 2
          rw [Kraken.Executable.program_apply_drop]
          arg 1
          (try delta $p)
          simp only [List.mapIdx_cons, List.mapIdx_nil,
                     List.drop_succ_cons, List.drop_zero, List.drop_nil,
                     Nat.add_zero, Nat.zero_add, Nat.reduceAdd])
      let startEventuallyConv ← `(tactic|
        ((try
           conv =>
             arg 1
             ext
             ext
             arg 2
             dsimp only)
         conv =>
           arg 2
           (try rw [Kraken.Executable.startAddr_apply])
           rw [Executable.directivesFromStart]
           (try delta $p)
           arg 1
           simp only [List.mapIdx_cons, List.mapIdx_nil,
                      Nat.add_zero, Nat.zero_add, Nat.reduceAdd]))
      let startExecConv ← `(tactic|
        conv =>
          arg 2
          (try rw [Kraken.Executable.startAddr_apply])
          (try rw [Kraken.Executable.program_apply])
          (try rw [Executable.directivesFromStart])
          (try delta $p)
          arg 1
          simp only [List.mapIdx_cons, List.mapIdx_nil,
                     Nat.add_zero, Nat.zero_add, Nat.reduceAdd])
      match s? with
      | none =>
        match k?, n? with
        | _, some n =>
          let k := k?.getD (Syntax.mkNumLit "0")
          evalTactic (← `(tactic| (refine $sliceThm $k $n _ (by kaddr $p) ?_; $sliceConv)))
        | some k, none =>
          evalTactic (← `(tactic| (refine $atThm $k _ (by kaddr $p) ?_; $dropConv)))
        | none, none =>
          let isEventually := isTraced || isTracedAccum || (← whnfR (← instantiateMVars (← getMainTarget))).getAppFn'.constName? == some ``Eventually
          if isEventually then
            evalTactic (← `(tactic| (apply $cpsThm; $startEventuallyConv)))
          else
            evalTactic (← `(tactic| ((try unfold Kraken.Executable.Exec Kraken.Executable.ExecTraced); $startExecConv)))
      | some s =>
        let statePat ← mkStateDestructPat s
        match k?, n? with
        | _, some n =>
          let k := k?.getD (Syntax.mkNumLit "0")
          evalTactic (← `(tactic|
            (refine $sliceThm (prog := $p) $k $n _ (s := $s) (by kaddr $p) ?_
             let ss := $s
             change (Kraken.Effects.All _ (@Directives.interp _ _ _ (Kraken.Executable.labels _) _ ss _ _))
             obtain $statePat:rcasesPat := $s
             (try dsimp only at *)
             $sliceConv)))
        | some k, none =>
          evalTactic (← `(tactic|
            (refine $atThm (prog := $p) $k _ (s := $s) (by kaddr $p) ?_
             let ss := $s
             change (Kraken.Effects.All _ (@Directives.interp _ _ _ (Kraken.Executable.labels _) _ ss _ _))
             obtain $statePat:rcasesPat := $s
             (try dsimp only at *)
             $dropConv)))
        | none, none =>
          let isEventually := isTraced || isTracedAccum || (← whnfR (← instantiateMVars (← getMainTarget))).getAppFn'.constName? == some ``Eventually
          if isEventually then
            evalTactic (← `(tactic|
              (apply $cpsThm
               let ss := $s
               change (Kraken.Effects.All _ (@Directives.interp _ _ _ (Kraken.Executable.labels _) _ ss _ _))
               obtain $statePat:rcasesPat := $s
               (try dsimp only at *)
               $startEventuallyConv)))
          else
            evalTactic (← `(tactic|
              ((try unfold Kraken.Executable.Exec Kraken.Executable.ExecTraced)
               let ss := $s
               change (Kraken.Effects.All _ (@Directives.interp _ _ _ _ _ ss _ _))
               obtain $statePat:rcasesPat := $s
               (try dsimp only at *)
               $startExecConv)))

/-! ### Constant-Time Packing, Introduction, and `kdone` -/

/-- Pack curried secret universal quantifiers after `s₀` into a single tuple so that
`tailrec_loop_cps_traced` can be applied directly to a `Spec (trace := some tr)` goal. -/
elab "kpack_secrets" : tactic => do
  evalTactic (← `(tactic|
    (simp only [Kraken.Executable.Spec, forall_prod_curry]
     rw [exists_forall_unpack_first]
     dsimp only)))

/-- Peel a leading `CtEventually` or `∃ tr, ...` trace witness (deferring unification to `kdone`)
and introduce universal / precondition binders with `rintro`. -/
elab "kintro" pats:(colGt rcasesPat)* : tactic =>
  withMainContext do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    if target.getAppFn'.constName? == some ``CtEventually then
      evalTactic (← `(tactic| unfold CtEventually))
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    if target.getAppFn'.constName? == some ``Exists then
      evalTactic (← `(tactic| (refine ⟨?_, ?_⟩; rotate_left)))
    evalTactic (← `(tactic| (try unfold Kraken.LoopAuto)))
    unless pats.isEmpty do
      evalTactic (← `(tactic| rintro $[$pats:rcasesPat]*))
    evalTactic (← `(tactic| (try unfold Kraken.LoopAuto at *)))
    evalTactic (← `(tactic| (try dsimp only at *)))

private def unifyTraceWitness (trExpected trActual : Expr) : TacticM Unit := do
  let savedDepth := (← getMCtx).depth
  let ok ← withAssignableSyntheticOpaque do
    if trExpected.getAppFn.isMVar then
      let decl ← trExpected.getAppFn.mvarId!.getDecl
      modifyMCtx fun mctx => { mctx with depth := decl.depth }
    try
      isDefEq trExpected trActual
    finally
      modifyMCtx fun mctx => { mctx with depth := savedDepth }
  unless ok do
    throwError "kdone: leakage trace depends on secret state and cannot unify with public trace:\n  expected: {trExpected}\n  actual:   {trActual}"
  pruneSolvedGoals

/-- Finish a stepped `TracedEventually`, `ExecTraced`, or `Eventually` goal, unifying any
synthetic-opaque trace witness metavariable with the accumulated concrete leakage trace. -/
elab "kdone" : tactic =>
  withMainContext do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    if target.isAppOfArity ``Eventually 4 then
      let postArg := (target.getArg! 2).consumeMData
      let stateArg := (target.getArg! 3).consumeMData
      if postArg.isAppOfArity ``TracedGoal 3 && stateArg.isAppOfArity ``Prod.mk 4 then
        let trExpected := (← instantiateMVars (postArg.getArg! 2)).consumeMData
        let trActual := (← instantiateMVars (stateArg.getArg! 3)).consumeMData
        unifyTraceWitness trExpected trActual
        evalTactic (← `(tactic| apply TracedEventually.done))
      else
        evalTactic (← `(tactic| apply Eventually.done))
    else if target.isAppOfArity ``TracedGoal 4 then
      let stateArg := (target.getArg! 3).consumeMData
      if stateArg.isAppOfArity ``Prod.mk 4 then
        let trExpected := (← instantiateMVars (target.getArg! 2)).consumeMData
        let trActual := (← instantiateMVars (stateArg.getArg! 3)).consumeMData
        unifyTraceWitness trExpected trActual
        evalTactic (← `(tactic| apply TracedGoal.done))
      else
        evalTactic (← `(tactic| apply TracedGoal.done))
    else
      evalTactic (← `(tactic| apply Eventually.done))

end
