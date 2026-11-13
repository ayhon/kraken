module

public import Kraken.Tactics.Prologue
public import Kraken.Tactics.Frame
public import Kraken.Tactics.Step

/-!
# Block and Loop Composition Tactics (`kfinish`, `kcall`, `kloop`, `kloop_exit`, `kloop_next`)

High-level proof tactics for finishing straight-line subgoals (`kfinish`), sequencing block
specifications (`kcall`), and reasoning about tail-recursive and constant-time loops
(`kloop`, `kloop_exit`, `kloop_next`).
-/

public meta section

open Lean Meta Elab Tactic Kraken Kraken.Tactic

/-! ### The `kfinish` Tactic -/

/-- Finish a goal (running `kstep` first if the goal is still an unstepped `Effects.All`): apply
`kdone` (`Eventually.done` / `TracedEventually.done` / `TracedGoal.done`) if needed, zeta-reduce and
normalise the goal and hypotheses (`dsimp +zetaDelta only [extra lemmas] at *`, the `BitVec`/`UInt64`
normal form used by `kstep`, then `simp only [extra lemmas, ↓reduceIte]` on the goal), split
conjunctions and `Prop`-valued structures, and discharge the components by `rfl`, `trivial`,
`assumption`, `omega`, `kaddr p` (label/address goals), `kframe` (register frames), or `ecancel`
(separation-logic goals). Components that cannot be discharged are left to the user, in order of
appearance. -/
syntax (name := kfinish) "kfinish" ident ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

elab_rules : tactic
  | `(tactic| kfinish $p:ident $[[$lemmas,*]]?) => withMainContext do
    let lemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) :=
      match lemmas with | some l => l.getElems | none => #[]
    let goalsBefore := (← getUnsolvedGoals).length
    if isEffectsAll (← instantiateMVars (← getMainTarget)) then
      evalTactic (← `(tactic| kstep))
      if (← getUnsolvedGoals).length > goalsBefore ||
         ((← getUnsolvedGoals).length > 0 && isEffectsAll (← instantiateMVars (← getMainTarget))) then
        return
    withMainContext do
    let tgt := (← instantiateMVars (← getMainTarget)).consumeMData
    if tgt.isAppOfArity ``Eventually 4 || tgt.isAppOfArity ``TracedGoal 4 then
      evalTactic (← `(tactic| kdone))
    evalTactic (← `(tactic| (try unfold Kraken.LoopAuto at *)))
    evalTactic (← `(tactic| (try dsimp +zetaDelta only [$lemmas,*] at *)))
    if (← getUnsolvedGoals).isEmpty then return
    withMainContext do
    let nfStx ← (normalFormLemmas ++ [``UInt64.toBitVec_add, ``UInt64.toBitVec_sub,
        ``UInt64.toBitVec_ofNat, ``Bool.false_eq_true, ``Bool.true_eq_false,
        ``beq_self_eq_true, ``bne_self_eq_false]).filterMapM fun n => do
      if (← getEnv).contains n then
        some <$> `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
      else pure none
    let nfStx := nfStx.toArray.push (← `(Lean.Parser.Tactic.simpLemma| ↓reduceIte))
    let nfStx := nfStx.push (← `(Lean.Parser.Tactic.simpLemma| kcond))
    evalTactic (← `(tactic| (try simp only [BitVec.shiftLeft_zero, BitVec.zero_or, BitVec.or_zero,
      BitVec.xor_self, UInt64.toNat_toBitVec, UInt64.toBitVec_ofBitVec, UInt64.toBitVec_add,
      UInt64.toBitVec_sub, UInt64.toBitVec_ofNat, kcond] at *)))
    evalTactic (← `(tactic| (try simp +decide only [$nfStx,*])))
    if (← getUnsolvedGoals).isEmpty then return
    let lemmaNames : Array Name := lemmas.filterMap fun l =>
      match l.raw.find? (·.isIdent) with
      | some id => some id.getId
      | none => none
    let hyps : Array Ident ← withMainContext do
      let mut acc := #[]
      for decl in (← getLCtx) do
        if decl.isImplementationDetail || decl.userName.hasMacroScopes then continue
        if lemmaNames.contains decl.userName then continue
        if ← isProp decl.type then acc := acc.push (mkIdent decl.userName)
      pure acc
    let frameEqs ← frameEqsInContext
    let frameStx ← frameEqs.mapM fun e => do
      let t ← Term.exprToSyntax e
      `(Lean.Parser.Tactic.simpLemma| $t:term)
    let allLemmas := lemmas ++ frameStx ++ #[← `(Lean.Parser.Tactic.simpLemma| ↓reduceIte)]
    evalTactic (← `(tactic| (try simp only [$allLemmas,*] at $hyps* ⊢)))
    if (← getUnsolvedGoals).isEmpty then return
    let leaves ← splitConjGoals (← getMainGoal)
    let mut remaining : List MVarId := []
    for g in leaves do
      if ← g.isAssigned then continue
      setGoals [g]
      let t := (← instantiateMVars (← g.getType)).consumeMData
      if t.isAppOf ``Kraken.RegFile.EqExcept || t.isAppOf ``Kraken.RegFile.EqOn then
        unless ← tryClose (← `(tactic| kframe)) do remaining := remaining ++ [g]
      else if mentionsConst t [``Kraken.Executable.label, ``Labels.label, ``Kraken.Executable.addrOf,
          ``Kraken.Layout.addrOf] then
        unless ← tryClose (← `(tactic| kaddr $p)) do remaining := remaining ++ [g]
      else if mentionsConst t [``Std.ExtHashMap.sep, ``List.At] then
        unless ← tryClose (← `(tactic| ecancel)) do remaining := remaining ++ [g]
      else
        -- Fast closers at reducible transparency so non-reducible user definitions and large
        -- power-of-two numerals are never unfolded on open subgoals.
        let closedFast ← g.withContext do
          if ← tryCatchRuntimeEx (withReducible g.assumptionCore) (fun _ => pure false) then
            pure true
          else if ← tryCatchRuntimeEx (do withReducible g.refl; pure true) (fun _ => pure false) then
            pure true
          else
            tryClose (← `(tactic| exact True.intro))
        if closedFast then continue
        let isBytePowRel :=
          (if t.isAppOfArity ``Eq 3 || t.isAppOfArity ``LE.le 4 || t.isAppOfArity ``LT.lt 4 ||
              t.isAppOfArity ``GE.ge 4 || t.isAppOfArity ``GT.gt 4 then
            let ty := (t.getArg! 0).consumeMData
            ty.isConstOf ``Int || ty.isConstOf ``Nat
          else
            false) &&
          mentionsConst t [``Int.ofBytes, ``Nat.ofBytes, ``HMod.hMod, ``HPow.hPow]
        if !isBytePowRel then
          let closedByDefEq ← withOptions (fun o => maxRecDepth.set o 256) do
            tryClose (← `(tactic| assumption)) <||> tryClose (← `(tactic| rfl))
          if closedByDefEq then
            continue
        let saved ← saveState
        let cleanG ← clearSepAndLets g (!isCalleeSavedEqType t)
        setGoals [cleanG]
        let runGrind := !isBytePowRel
        let closers : List (TSyntax `tactic) ←
          if runGrind then
            pure [← `(tactic| omega), ← `(tactic| simp), ← `(tactic| grind)]
          else
            pure [← `(tactic| omega), ← `(tactic| simp)]
        let mut closed := false
        for tac in closers do
          if !closed then
            closed ← tryClose tac
        if !closed then
          saved.restore
          remaining := remaining ++ [g]
    setGoals remaining

/-! ### Continuation and Loop-Auto Helpers -/

initialize registerTraceClass `Kraken.kcall

/-- For `h : a = b ∧ rest` or `h : a = b` where one side is a local variable not occurring in the
other, substitute the variable away (keeping `h : rest` in the first case). Eliminates the leading
`st.pc = …` conjunct of block postconditions. -/
private def substLeadingVarEq (h : Ident) : TacticM Unit := withMainContext do
  let some decl := (← getLCtx).findFromUserName? h.getId | return
  let t ← whnfR (← instantiateMVars decl.type)
  let isVarEq (e : Expr) : Bool :=
    let e := e.consumeMData
    let e := if e.isAppOfArity ``Kraken.LoopAuto 1 then (e.getArg! 0).consumeMData else e
    match e.eq? with
    | some (_, lhs, rhs) =>
      (lhs.isFVar && !rhs.containsFVar lhs.fvarId!) || (rhs.isFVar && !lhs.containsFVar rhs.fvarId!)
    | none => false
  if t.isAppOfArity ``And 2 && isVarEq (t.getArg! 0) then
    let hpc := mkIdent (← mkFreshUserName `hpc)
    evalTactic (← `(tactic| obtain ⟨$hpc:ident, $h:ident⟩ := $h:ident))
    evalTactic (← `(tactic| (try unfold Kraken.LoopAuto at $hpc:ident)))
    evalTactic (← `(tactic| subst $hpc:ident))
  else if isVarEq t then
    evalTactic (← `(tactic| (try unfold Kraken.LoopAuto at $h:ident)))
    evalTactic (← `(tactic| subst $h:ident))

/-- Introduce the continuation of a `bind` or loop rule: `rintro ⟨st, st_pc⟩ h`, beta-reduce `h`,
substitute a leading `st_pc = …` conjunct, peel and expand any `LoopAuto` register-frame conjunct,
and destructure the rest with `pat?`. -/
private def introContinuation (st h : Ident) (pat? : Option (TSyntax `rcasesPat)) :
    TacticM Unit := do
  let stPc := mkIdent (st.getId.appendAfter "_pc")
  let stPat ← `(rcasesPat| ⟨$st:ident, $stPc:ident⟩)
  let hPat ← `(rcasesPat| $h:ident)
  evalTactic (← `(tactic| rintro $stPat:rcasesPat $hPat:rcasesPat))
  evalTactic (← `(tactic| (try dsimp only at $h:ident)))
  try substLeadingVarEq h catch _ => pure ()
  withMainContext do
    if let some decl := (← getLCtx).findFromUserName? h.getId then
      let t := (← instantiateMVars decl.type).consumeMData
      if t.isAppOfArity ``And 2 && (t.getArg! 0).consumeMData.isAppOfArity ``Kraken.LoopAuto 1 then
        let inner := ((t.getArg! 0).consumeMData.getArg! 0).consumeMData
        if inner.isAppOf ``Kraken.RegFile.EqExcept || inner.isAppOf ``Kraken.RegFile.EqOn then
          let hFr := mkIdent `h_fr
          evalTactic (← `(tactic| obtain ⟨$hFr:ident, $h:ident⟩ := $h:ident))
          evalTactic (← `(tactic| (try unfold Kraken.LoopAuto at $hFr:ident)))
          evalTactic (← `(tactic| kframe_eqs $hFr:ident))
  if let some pat := pat? then
    evalTactic (← `(tactic| obtain $pat:rcasesPat := $h:ident))

/-- Peel and discharge leading `Kraken.LoopAuto` (`pc` and register-frame) conjuncts of a loop
invariant goal using `closePcGoal` and `kframe`. -/
private partial def peelAutoLoopGoals (prog? : Option Name) : TacticM Unit := withMainContext do
  if (← getUnsolvedGoals).isEmpty then return
  let g ← getMainGoal
  let t := (← instantiateMVars (← g.getType)).consumeMData
  unless t.isAppOfArity ``And 2 && (t.getArg! 0).consumeMData.isAppOfArity ``Kraken.LoopAuto 1 do
    return
  let inner := ((t.getArg! 0).consumeMData.getArg! 0).consumeMData
  evalTactic (← `(tactic| refine ⟨?_, ?_⟩))
  let [gHead, gTail] ← getGoals | return
  setGoals [gHead]
  evalTactic (← `(tactic| (try unfold Kraken.LoopAuto)))
  let closed ←
    if inner.isAppOf ``Kraken.RegFile.EqExcept || inner.isAppOf ``Kraken.RegFile.EqOn then
      tryClose (← `(tactic| kframe))
    else
      closePcGoal prog?
  if closed then
    setGoals [gTail]
    peelAutoLoopGoals prog?
  else
    let headGoals ← getGoals
    setGoals [gTail]
    peelAutoLoopGoals prog?
    setGoals (headGoals ++ (← getGoals))

private def rcasesPatIdent? (p : TSyntax `rcasesPat) : Option Name :=
  if p.raw.isOfKind ``Lean.Parser.Tactic.rcasesPat.one then
    match p.raw[0] with
    | .ident _ _ n _ => some n
    | _ => none
  else none

private def tagGoals (tag : Name) : TacticM Unit := do
  for g in (← getGoals) do
    g.setTag tag

/-- Build the `Kraken.LoopAuto` conjunct syntax terms for `writes`, `preserves`, `pc`, and
`at "label"` (ordered inner-to-outer). -/
private def mkLoopAutoConjunctStxs (prog? : Option Name) (stId : Ident) (s0Stx : Term)
    (atLbl? : Option StrLit) (pc? writes? preserves? : Option Term) : TacticM (Array Term) := do
  let extractRegIdents (val : Term) (key : Name) : TacticM (Array Ident) := do
    match val with
    | `([$ts:term,*]) =>
      ts.getElems.mapM fun t =>
        if t.raw.isIdent then pure ⟨t.raw⟩
        else throwErrorAt t "kloop: `{key}` expects register or view identifiers"
    | _ => throwErrorAt val "kloop: `{key}` expects `[r, …]`"
  let mut conjs : Array Term := #[]
  if let some wVal := writes? then
    let rs ← extractRegIdents wVal `writes
    conjs := conjs.push (← `(Kraken.LoopAuto (($stId).data.regs ≡ ($s0Stx).regs except [$rs,*])))
  if let some pVal := preserves? then
    let rs ← extractRegIdents pVal `preserves
    conjs := conjs.push (← `(Kraken.LoopAuto (($stId).data.regs ≡ ($s0Stx).regs on [$rs,*])))
  if let some e := pc? then
    conjs := conjs.push (← `(Kraken.LoopAuto (($stId).pc = $e)))
  if let some lbl := atLbl? then
    let some progName := prog?
      | throwError "kloop: could not determine program from goal for `at {lbl}`"
    let layoutId := mkIdent `layout
    let progId := mkIdent progName
    conjs := conjs.push (← `(Kraken.LoopAuto (($stId).pc = ($layoutId $progId).label $lbl)))
  return conjs

/-! ### The `kcall` Tactic -/

/-- `kcall e [with [st] pat]`: sequence the specification `e` of a block or sub-program into the
current `Eventually` goal via `Eventually.bind_at` (or `Eventually.bind_at_traced`).

`e` may prove `(layout p).Spec s (pc := …) (pre := …) (post := …)`, an `Eventually`, or a
`TracedEventually`; leading hypotheses of `e` that are not supplied (its preconditions) become
`pre` goals, closed automatically when they follow from the context. The program-counter side
condition is closed by `rfl`/`kaddr`. The continuation is introduced as `st : MachineData` with
`hst : post`, a leading `st.pc = …` conjunct is substituted, and `pat` destructures the rest. -/
syntax (name := kcall) "kcall " term (" with " (ppSpace colGt rcasesPat)+)? : tactic

elab_rules : tactic
  | `(tactic| kcall $e:term $[with $pats?*]?) => withKrakenRecDepth <| withMainContext do
    let pats : Array (TSyntax `rcasesPat) := pats?.getD #[]
    let (stName, hPat?) ← match pats with
      | #[] => pure (`st, none)
      | #[p] => pure (`st, some p)
      | #[s, p] =>
        match rcasesPatIdent? s with
        | some n => pure (n, some p)
        | none => throwErrorAt s "kcall: expected a name for the intermediate state"
      | _ => throwError "kcall: expected at most two patterns (`with [st] pat`)"
    let st := mkIdent stName
    let h := mkIdent (Name.mkSimple ("h" ++ stName.toString))
    if isEffectsAll (← instantiateMVars (← getMainTarget)) then
      evalTactic (← `(tactic| kstep))
    withMainContext do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    if target.isAppOf ``TracedEventually then
      evalTactic (← `(tactic| unfold TracedEventually))
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    unless target.isAppOfArity ``Eventually 4 do
      throwError "kcall: the goal must be an `Eventually` (introduce the specification first, e.g. with `kintro`):{indentExpr target}"
    let traced := (target.getArg! 1).consumeMData.getAppFn'.constName? == some ``step1Traced
    let prog? := findLayoutProg? target
    let callExpr ← Tactic.elabTerm e none (mayPostpone := true)
    let callType ← instantiateMVars (← inferType callExpr)
    let (args, _, _) ← forallMetaTelescopeReducing callType
    let callProof := mkAppN callExpr args
    let thm := if traced then ``Eventually.bind_at_traced else ``Eventually.bind_at
    let thmFn ← mkConstWithFreshMVarLevels thm
    let (xs, bis, _) ← forallMetaTelescopeReducing (← inferType thmFn)
    let some i := bis.findIdx? (·.isExplicit) | throwError "kcall: unexpected signature of {thm}"
    unless ← isDefEq (← inferType xs[i]!) (← inferType callProof) do
      throwError "kcall: `{e}` does not prove an `Eventually`{if traced then " (traced)" else ""} specification:{indentExpr callType}"
    let partialApp := mkAppN thmFn ((xs.extract 0 i).push callProof)
    let goal ← getMainGoal
    let newGoals ← goal.apply partialApp
    Term.synthesizeSyntheticMVarsNoPostponing
    let hpcGoal :: kGoal :: _ := newGoals
      | throwError "kcall: unexpected goals after applying {thm}"
    setGoals [hpcGoal]
    let pcClosed ← closePcGoal prog?
    let mut preGoals : Array MVarId := #[]
    for a in args do
      let m := a.mvarId!
      if ← m.isAssigned then continue
      let isProp ← m.withContext do isProp (← m.getType)
      unless isProp do
        throwError "kcall: could not infer the argument `{a}` of `{e}`:{indentExpr (← m.getType)}"
      m.setKind .syntheticOpaque
      unless ← tryCloseSimple m do
        m.setTag `pre
        preGoals := preGoals.push m
    setGoals [kGoal]
    trace[Kraken.kcall] "goals before intro: {(← getGoals).map (·.name)}; pre: {preGoals.map (·.name)}; newGoals: {newGoals.map (·.name)}"
    introContinuation st h hPat?
    let kGoals ← getGoals
    trace[Kraken.kcall] "goals after intro: {kGoals.map (·.name)}"
    unless pcClosed do hpcGoal.setTag `pc
    setGoals (kGoals ++ preGoals.toList ++ (if pcClosed then [] else [hpcGoal]))

/-! ### The `kloop`, `kloop_exit`, and `kloop_next` Tactics -/

syntax kloopArg := " (" ident " := " term ")"

/-- `kloop [at "label"] [(writes := […]) | (preserves := […])] (inv := P) [(exit := Q)]
(measure := v₀) [(ghost := g₀)] [(lt := r) (wf := h)] [(state := st)] [with v g pat]`:
apply the tail-recursive loop rule to an `Eventually` goal.

* `at "label"` (or `(pc := e)`) prepends `st.pc = (layout prog).label "label"` to `inv`, discharging
  it automatically in `init` and `kloop_next` and substituting it in `body`.
* `(writes := [r, …])` / `(preserves := [r, …])` prepends `st.data.regs ≡ s₀.regs except/on [r, …]`
  to `inv`, discharging it with `kframe` in `init` and `kloop_next` and introducing `h_fr` together
  with its `kframe_eqs` equations (`h_fr_<reg>`, `h_fr_<view>`) in `body`.
* `P : Measure → Ghost → State → Prop` (or `Measure → State → Prop` without `ghost`) is the loop
  invariant, `v₀`/`g₀` the initial measure and ghost; `lt`/`wf` default to `<` on `Nat`.
* Without `exit`, `tailrec_loop_simple` is used: goals `init : P v₀ g₀ s` and `body`, whose
  conclusion is `post mid ∨ ∃ v' g', P v' g' mid ∧ v' < v` (see `kloop_exit` / `kloop_next`).
* With `exit`, `tailrec_loop_cps` is used: `Q` may have type `State → Prop` (1 arg),
  `Measure → State → Prop` (2 args), or `Measure → Ghost → State → Prop` (3 args), producing goals
  `init : Eventually (Q v₀ g₀ ∨ P v₀ g₀) s`,
  `body` (conclusion `Q v g mid ∨ ∃ v' g', P v' g' mid ∧ v' < v ∧ (∀ t, Q v' g' t → Q v g t)`)
  and `exit : ∀ st, Q v₀ g₀ st → Eventually post st`.

In `body` the measure, ghost, state and invariant hypothesis are introduced as `v g st hst`
(names/patterns from `state :=` and `with`), with a leading `st.pc = …` conjunct substituted.

**Constant-time loops.** With `(pub := pub₀)` the goal is a traced specification
(`∃ tr, ∀ s₀ sec, pre s₀ sec → TracedEventually e (post s₀ sec) tr ⟨s₀, pc⟩`, as produced by
`kpack_secrets`; a `Spec … (trace := some tr)` goal is packed first) and `tailrec_loop_cps_traced`
is used: `inv`/`exit` have type `Measure → Pub → MD → Secret → Ghost → State → Prop` (or without
`Ghost` when `ghost` is omitted; `exit` defaults to `post`), `ghost` is `g₀ : MD → Secret → Ghost`,
and `(pubinv := Inv)` (default `fun _ _ => True`) is the invariant on measure and public data.
Goals: `init` (`(∃ tr, …) ∨ (Inv v₀ pub₀ ∧ ∃ tr, …)`), `body` with `v pub hpub` introduced
(`(∃ tr, …) ∨ ∃ v' pub', lt v' v ∧ Inv v' pub' ∧ ∃ tr, …`) and (when `exit` is given) `post`;
`kloop_exit`, `kloop_next v' pub'` and `kintro` take it from there. -/
syntax (name := kloop) "kloop" (" at " str)? (ppSpace kloopArg)+ (" with " (ppSpace colGt rcasesPat)+)? : tactic

elab_rules : tactic
  | `(tactic| kloop $[at $atLbl?]? $args* $[with $pats?*]?) => withKrakenRecDepth <| withMainContext do
    let pats : Array (TSyntax `rcasesPat) := pats?.getD #[]
    let mut inv? : Option Term := none
    let mut exit? : Option Term := none
    let mut measure? : Option Term := none
    let mut ghost? : Option Term := none
    let mut lt? : Option Term := none
    let mut wf? : Option Term := none
    let mut pub? : Option Term := none
    let mut pubinv? : Option Term := none
    let mut pc? : Option Term := none
    let mut writes? : Option Term := none
    let mut preserves? : Option Term := none
    let mut stName := `st
    for arg in args do
      let key := arg.raw[1].getId
      let val : Term := ⟨arg.raw[3]⟩
      match key with
      | `inv => inv? := some val
      | `exit => exit? := some val
      | `measure => measure? := some val
      | `ghost => ghost? := some val
      | `lt => lt? := some val
      | `wf => wf? := some val
      | `pub => pub? := some val
      | `pubinv => pubinv? := some val
      | `pc => pc? := some val
      | `writes => writes? := some val
      | `preserves => preserves? := some val
      | `state =>
        unless val.raw.isIdent do throwErrorAt val "kloop: `state` expects a name"
        stName := val.raw.getId
      | _ => throwErrorAt arg "kloop: unknown argument `{key}` (expected inv, exit, measure, ghost, lt, wf, pub, pubinv, pc, writes, preserves, state)"
    let some inv := inv? | throwError "kloop: missing `(inv := …)`"
    let some v0Stx := measure? | throwError "kloop: missing `(measure := …)`"
    -- Constant-time loop: delegate to `tailrec_loop_cps_traced`.
    if let some pub0 := pub? then
      let pubInv ← match pubinv? with
        | some t => pure t
        | none => `(fun _ _ => True)
      let target := (← instantiateMVars (← getMainTarget)).consumeMData
      let prog? := findLayoutProg? target
      if target.find? (·.isConstOf ``Kraken.Executable.Spec) |>.isSome then
        evalTactic (← `(tactic| kpack_secrets))
      let g0 ← match ghost? with
        | some g => pure g
        | none => `(fun _ _ => ())
      let liftCtNoGhost (f : Term) : TacticM Term := do
        match ghost? with
        | some _ => pure f
        | none => `(fun v pub s₀ sec _ st => $f v pub s₀ sec st)
      let mut invCt ← liftCtNoGhost inv
      if atLbl?.isSome || pc?.isSome || writes?.isSome || preserves?.isSome then
        let vId := mkIdent (← mkFreshUserName `v)
        let pubId := mkIdent (← mkFreshUserName `pub)
        let s0Id := mkIdent (← mkFreshUserName `s₀)
        let secId := mkIdent (← mkFreshUserName `sec)
        let gId := mkIdent (← mkFreshUserName `g)
        let stId := mkIdent (← mkFreshUserName `st)
        let conjs ← mkLoopAutoConjunctStxs prog? stId s0Id atLbl? pc? writes? preserves?
        let mut bodyStx : Term ← `($invCt $vId $pubId $s0Id $secId $gId $stId)
        for c in conjs do
          bodyStx ← `($c ∧ $bodyStx)
        invCt ← `(fun $vId $pubId $s0Id $secId $gId $stId => $bodyStx)
      let exitQ ← match exit? with
        | some q => liftCtNoGhost q
        | none => `(fun _ _ s₀ sec _ => _)
      let mut rule : Term ← `(tailrec_loop_cps_traced _ (Inv := $pubInv) (P := $invCt) (Q := $exitQ)
        (v0 := $v0Stx) (pub0 := $pub0) (g0 := $g0))
      match lt?, wf? with
        | some l, some w => rule ← `($rule (lt := $l) (Hwf := $w))
        | none, none => pure ()
        | _, _ => throwError "kloop: `lt` and `wf` must be given together"
      evalTactic (← `(tactic| apply $rule))
      let [gInit, gBody, gPost] ← getGoals
        | throwError "kloop: unexpected goals after applying `tailrec_loop_cps_traced`"
      let postGoals ← match exit? with
        | some _ =>
          setGoals [gPost]
          evalTactic (← `(tactic| (try dsimp only)))
          tagGoals `post
          getGoals
        | none =>
          setGoals [gPost]
          evalTactic (← `(tactic| exact ⟨[], fun _ _ _ h => TracedEventually.done h⟩))
          pure []
      setGoals [gInit]
      evalTactic (← `(tactic| (try dsimp only)))
      tagGoals `init
      let initGoals ← getGoals
      setGoals [gBody]
      let vPat ← match pats[0]? with
        | some p => pure p
        | none => `(rcasesPat| v)
      let pubPat ← match pats[1]? with
        | some p => pure p
        | none => `(rcasesPat| pub)
      let hPat ← match pats[2]? with
        | some p => pure p
        | none => `(rcasesPat| hpub)
      evalTactic (← `(tactic| rintro $vPat:rcasesPat $pubPat:rcasesPat $hPat:rcasesPat))
      evalTactic (← `(tactic| (try dsimp only)))
      tagGoals `body
      let bodyGoals ← getGoals
      setGoals (initGoals ++ bodyGoals ++ postGoals)
      return
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    if target.isAppOf ``TracedEventually then
      evalTactic (← `(tactic| unfold TracedEventually))
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    unless target.isAppOfArity ``Eventually 4 do
      throwError "kloop: the goal must be an `Eventually`:{indentExpr target}"
    let prog? := findLayoutProg? target
    let trans := target.getArg! 1
    let post := target.getArg! 2
    let initial := target.getArg! 3
    let stateType ← inferType initial
    let postType ← mkArrow stateType (mkSort .zero)
    let v0 ← Tactic.elabTerm v0Stx none
    let measureType ← instantiateMVars (← inferType v0)
    let (g0, ghostType) ← match ghost? with
      | some gStx =>
        let g0 ← Tactic.elabTerm gStx none
        pure (g0, ← instantiateMVars (← inferType g0))
      | none => pure (mkConst ``Unit.unit, mkConst ``Unit)
    let invType ← mkArrow measureType (← mkArrow ghostType postType)
    let invTypeNoGhost ← mkArrow measureType postType
    let lift1 (f : Expr) : MetaM Expr :=
      withLocalDeclD `v measureType fun v =>
        withLocalDeclD `g ghostType fun g =>
          withLocalDeclD `st stateType fun s => do
            mkLambdaFVars #[v, g, s] (mkApp f s).headBeta
    let lift2 (f : Expr) : MetaM Expr :=
      withLocalDeclD `v measureType fun v =>
        withLocalDeclD `g ghostType fun g =>
          withLocalDeclD `st stateType fun s => do
            mkLambdaFVars #[v, g, s] (mkAppN f #[v, s]).headBeta
    let tryElab (stx : Term) (ty : Expr) : TacticM (Option Expr) := do
      let s ← saveState
      try
        let e ← Tactic.withoutRecover (Tactic.elabTermEnsuringType stx ty)
        Term.synthesizeSyntheticMVarsNoPostponing
        if (← getThe Core.State).messages.hasErrors then
          s.restore
          return none
        return some e
      catch _ =>
        s.restore
        return none
    let elabInv (stx : Term) : TacticM Expr := do
      match ghost? with
      | some _ =>
        if let some f ← tryElab stx invType then return f
        if let some f ← tryElab stx invTypeNoGhost then return ← lift2 f
        Tactic.elabTermEnsuringType stx invType
      | none =>
        lift2 (← Tactic.elabTermEnsuringType stx invTypeNoGhost)
    let elabExit (stx : Term) : TacticM Expr := do
      if let some f ← tryElab stx postType then return ← lift1 f
      if let some f ← tryElab stx invTypeNoGhost then return ← lift2 f
      match ghost? with
      | some _ => Tactic.elabTermEnsuringType stx invType
      | none => lift2 (← Tactic.elabTermEnsuringType stx invTypeNoGhost)
    let P_user ← elabInv inv
    let P ←
      if atLbl?.isNone && pc?.isNone && writes?.isNone && preserves?.isNone then
        pure P_user
      else do
        let s0Expr ←
          if initial.consumeMData.isAppOfArity ``Kraken.MachineState.mk 3 then
            pure (initial.consumeMData.getArg! 1)
          else
            mkAppM ``Kraken.MachineState.data #[initial]
        let s0Stx : Term ←
          if s0Expr.isFVar then
            pure (mkIdent (← s0Expr.fvarId!.getUserName))
          else
            Term.exprToSyntax s0Expr
        let stTmpId := mkIdent (← mkFreshUserName `st)
        let conjs ← mkLoopAutoConjunctStxs prog? stTmpId s0Stx atLbl? pc? writes? preserves?
        withLocalDeclD `v measureType fun v =>
          withLocalDeclD `g ghostType fun g =>
            withLocalDeclD stTmpId.getId stateType fun s => do
              let mut body := (mkAppN P_user #[v, g, s]).headBeta
              for c in conjs do
                let cExpr ← Tactic.elabTermEnsuringType c (mkSort .zero)
                body := mkApp2 (mkConst ``And) cExpr body
              mkLambdaFVars #[v, g, s] body
    let Q? ← exit?.mapM elabExit
    let (lt, wf) ← match lt?, wf? with
      | some l, some w =>
        let lt ← Tactic.elabTermEnsuringType l (← mkArrow measureType (← mkArrow measureType (mkSort .zero)))
        let wf ← Tactic.elabTermEnsuringType w (← mkAppM ``WellFounded #[lt])
        pure (lt, wf)
      | none, none =>
        unless measureType.isConstOf ``Nat do
          throwError "kloop: give `(lt := …) (wf := …)` for a measure of type{indentExpr measureType}"
        let lt ← Tactic.elabTerm (← `(fun a b : Nat => a < b)) none
        let wf ← Tactic.elabTerm (← `(Nat.lt_wfRel.wf)) none
        pure (lt, wf)
      | _, _ => throwError "kloop: `lt` and `wf` must be given together"
    Term.synthesizeSyntheticMVarsNoPostponing
    let proof ← match Q? with
      | none => mkAppM ``tailrec_loop_simple #[trans, post, initial, P, lt, wf, v0, g0]
      | some Q => mkAppM ``tailrec_loop_cps #[trans, post, initial, P, Q, lt, wf, v0, g0]
    let goal ← getMainGoal
    let newGoals ← goal.apply proof
    let (gInit, gBody, gExit?) ← match Q?, newGoals with
      | none, [gInit, gBody] => pure (gInit, gBody, none)
      | some _, [gInit, gBody, gExit] => pure (gInit, gBody, some gExit)
      | _, _ => throwError "kloop: unexpected goals after applying the loop rule"
    -- `init`
    setGoals [gInit]
    evalTactic (← `(tactic| (try dsimp only)))
    peelAutoLoopGoals prog?
    tagGoals `init
    let initGoals ← getGoals
    -- `body`
    setGoals [gBody]
    let vPat ← match pats[0]? with
      | some p => pure p
      | none => `(rcasesPat| v)
    let gPat ← match pats[1]? with
      | some p => pure p
      | none => `(rcasesPat| g)
    evalTactic (← `(tactic| rintro $vPat:rcasesPat $gPat:rcasesPat))
    let st := mkIdent stName
    let h := mkIdent (Name.mkSimple ("h" ++ stName.toString))
    introContinuation st h pats[2]?
    tagGoals `body
    let bodyGoals ← getGoals
    -- `exit`
    let exitGoals ← match gExit? with
      | none => pure []
      | some gExit =>
        setGoals [gExit]
        introContinuation st h none
        tagGoals `exit
        getGoals
    setGoals (initGoals ++ bodyGoals ++ exitGoals)

/-- Reduce a loop-body/entry goal to its disjunction `post ∨ …` (running `kstep` and applying
`Eventually.done` if needed) and return the right disjunct. -/
private def kloopDisjunct : TacticM Expr := do
  if isEffectsAll (← instantiateMVars (← getMainTarget)) then
    evalTactic (← `(tactic| kstep))
  let t := (← instantiateMVars (← getMainTarget)).consumeMData
  if t.isAppOfArity ``Eventually 4 then
    evalTactic (← `(tactic| apply Eventually.done))
  evalTactic (← `(tactic| (try dsimp only)))
  let t := (← instantiateMVars (← getMainTarget)).consumeMData
  unless t.isAppOfArity ``Or 2 do
    throwError "expected a loop goal `post ∨ …` (see `kloop`):{indentExpr t}"
  return (t.getArg! 1).consumeMData

/-- Leave the loop: select the left (`post`/`Q`) disjunct of a `kloop` body or entry goal. -/
elab "kloop_exit" : tactic => withMainContext do
  discard <| kloopDisjunct
  evalTactic (← `(tactic| refine Or.inl ?_))
  evalTactic (← `(tactic| (try dsimp only)))

/-- `kloop_next v' [g']`: go round the loop again with measure `v'` and ghost `g'` (`()` for a
unit ghost). Produces the goal `P v' g' mid` (first), tries to close the decrease goal `v' < v`
with `omega`/`decide` and the `Q`-monotonicity goal of `tailrec_loop_cps` with
`fun _ h => h`, and leaves whatever remains. Without arguments, selects the right disjunct of a
`kloop … (exit := Q)` entry goal (`P v₀ g₀ mid`). -/
elab "kloop_next" vs:(ppSpace colGt term:max)* : tactic => withMainContext do
    let rhs ← kloopDisjunct
    withMainContext do
    if !rhs.isAppOfArity ``Exists 2 then
      unless vs.isEmpty do
        throwError "kloop_next: this goal has no measure to supply:{indentExpr rhs}"
      let prog? := findLayoutProg? rhs
      evalTactic (← `(tactic| refine Or.inr ?_))
      evalTactic (← `(tactic| (try dsimp only)))
      peelAutoLoopGoals prog?
      return
    let vLam := (rhs.getArg! 1).consumeMData
    let ghostType? : Option Expr :=
      if vLam.isLambda then
        let inner := vLam.bindingBody!.consumeMData
        if inner.isAppOfArity ``Exists 2 then some (inner.getArg! 0) else none
      else none
    let unitStx ← `(Unit.unit)
    let (v', g') ← match vs with
      | #[v'] =>
        if ghostType?.any (fun t => t.isConstOf ``Unit || t.isConstOf ``PUnit) then
          pure (v', unitStx)
        else
          throwError "kloop_next: the loop has a ghost state; use `kloop_next v' g'`{indentExpr rhs}"
      | #[v', g'] => pure (v', g')
      | _ => throwError "kloop_next: expected `kloop_next v' [g']`"
    let isTraced : Bool :=
      if vLam.isLambda then
        let inner := vLam.bindingBody!.consumeMData
        if inner.isAppOfArity ``Exists 2 then
          let pubLam := (inner.getArg! 1).consumeMData
          if pubLam.isLambda then
            let body := pubLam.bindingBody!.consumeMData
            body.isAppOfArity ``And 2 && (body.getArg! 1).consumeMData.isAppOfArity ``And 2 &&
              ((body.getArg! 1).consumeMData.getArg! 1).consumeMData.isAppOfArity ``Exists 2
          else false
        else false
      else false
    if isTraced then
      evalTactic (← `(tactic| refine Or.inr ⟨$v', $g', ?dec, ?inv, ?step⟩))
      let [gDec, gInv, gStep] ← getGoals | throwError "kloop_next: unexpected goals"
      let mut side : List MVarId := []
      for g in [gDec, gInv] do
        setGoals [g]
        evalTactic (← `(tactic| (try dsimp only)))
        unless (← tryClose (← `(tactic| omega))) || (← tryClose (← `(tactic| decide))) ||
            (← tryClose (← `(tactic| trivial))) do
          side := side ++ [g]
      setGoals [gStep]
      evalTactic (← `(tactic| (try dsimp only)))
      setGoals ((← getGoals) ++ side)
      return
    let prog? := findLayoutProg? rhs
    evalTactic (← `(tactic| refine Or.inr ⟨$v', $g', ?inv, ?rest⟩))
    let gs ← getGoals
    let [gInv, gRest] := gs | throwError "kloop_next: unexpected goals"
    setGoals [gRest]
    evalTactic (← `(tactic| (try dsimp only)))
    let restT := (← instantiateMVars (← getMainTarget)).consumeMData
    let mut side : List MVarId := []
    if restT.isAppOfArity ``And 2 then
      evalTactic (← `(tactic| refine ⟨?dec, ?mono⟩))
      let [gDec, gMono] ← getGoals | throwError "kloop_next: unexpected goals"
      setGoals [gDec]
      unless (← tryClose (← `(tactic| omega))) || (← tryClose (← `(tactic| decide))) do
        side := side ++ [gDec]
      setGoals [gMono]
      unless ← tryClose (← `(tactic| exact fun _ h => h)) do
        side := side ++ [gMono]
    else
      unless (← tryClose (← `(tactic| omega))) || (← tryClose (← `(tactic| decide))) do
        side := side ++ [gRest]
    setGoals [gInv]
    evalTactic (← `(tactic| (try dsimp only)))
    peelAutoLoopGoals prog?
    setGoals ((← getGoals) ++ side)

end
