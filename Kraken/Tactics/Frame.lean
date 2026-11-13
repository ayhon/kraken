module

public import Kraken.Frame
public import Kraken.Tactics.Util

/-!
# Register-Frame Automation (`kframe`, `kframe_eqs`)

Tactics for extracting register and derived-view preservation equations from `r' ≡ r except W` /
`r' ≡ r on V` hypotheses (`kframe_eqs`) and discharging register-frame goals (`kframe`).
-/

public meta section

open Lean Meta Elab Tactic Kraken Kraken.Tactic

/-! ### Register-Set Membership and Projection Helpers -/

/-- Index of `n` in `elems` up to reducible definitional equality. -/
private def findRegIdx? (elems : Array Expr) (n : Expr) : MetaM (Option Nat) := do
  for h : i in [0:elems.size] do
    if ← withReducible (isDefEq elems[i] n) then return some i
  return none

/-- Proof of `n ∈ W` (`W` a literal list, `n` its `i`-th element). -/
private partial def mkMemProof (α n W : Expr) (i : Nat) : MetaM Expr := do
  let W ← whnfD W
  if i == 0 then
    mkAppOptM ``List.mem_cons_self #[α, n, W.getArg! 2]
  else
    let rest ← mkMemProof α n (W.getArg! 2) (i - 1)
    mkAppM ``List.mem_cons_of_mem #[W.getArg! 1, rest]

/-- Proof of `n ∉ W` for a literal list `W` of register names (by `decide` on each `≠`). -/
private partial def mkNotMemProof (α n W : Expr) : MetaM Expr := do
  let W ← whnfD W
  if W.isAppOfArity ``List.nil 1 then
    mkAppOptM ``List.not_mem_nil #[α, n]
  else
    let hne ← mkDecideProof (← mkAppM ``Ne #[n, W.getArg! 1])
    let hrest ← mkNotMemProof α n (W.getArg! 2)
    mkAppM ``List.not_mem_cons_of_ne_of_not_mem #[hne, hrest]

/-- Short register name for hypothesis naming: the last constructor name occurring in `n`. -/
private def regNameString (n : Expr) : String :=
  match n.getAppFn.constName? with
  | some c =>
    if n.getAppNumArgs > 0 then
      match (n.getArg! (n.getAppNumArgs - 1)).getAppFn.constName? with
      | some c' => c'.getString!
      | none => c.getString!
    else c.getString!
  | none => "reg"

/-- Present a raw structure projection `x.i` as the projection function `S.f x`. -/
private def projFnApp (e : Expr) : MetaM Expr := do
  let .proj S i x := e | return e
  let env ← getEnv
  let some fname := (getStructureFields env S)[i]? | return e
  let some pfn := getProjFnForField? env S fname | return e
  try mkAppM pfn #[x] catch _ => return e

/-! ### Frame Equation Extraction and View Proofs -/

/-- For `h : RegFile.EqExcept W r' r` or `h : RegFile.EqOn vs r' r`, return the field/view
equations `r'.f = r.f` paired with each register or view's short name. -/
def frameEqsOf (h : Expr) : MetaM (Array (String × Expr)) := do
  let hType := (← instantiateMVars (← inferType h)).consumeMData
  if hType.isAppOfArity ``Kraken.RegFile.EqExcept 5 then
    let args := hType.getAppArgs
    let R := args[0]!; let inst := args[1]!; let W := args[2]!; let r' := args[3]!; let r := args[4]!
    let nameTy ← whnfD (mkApp2 (mkConst ``Kraken.RegFile.Name) R inst)
    let names ← literalListElems (mkApp2 (mkConst ``Kraken.RegFile.names) R inst)
    let wElems ← literalListElems W
    let mut acc := #[]
    for n in names do
      if (← findRegIdx? wElems n).isSome then continue
      let hn ← mkNotMemProof nameTy n W
      let lhs ← projFnApp (← whnfD (mkApp4 (mkConst ``Kraken.RegFile.get) R inst r' n))
      let rhs ← projFnApp (← whnfD (mkApp4 (mkConst ``Kraken.RegFile.get) R inst r n))
      let prf ← mkExpectedTypeHint (mkApp2 h n hn) (← mkEq lhs rhs)
      acc := acc.push (regNameString n, prf)
    return acc
  else if hType.isAppOfArity ``Kraken.RegFile.EqOn 4 then
    let args := hType.getAppArgs
    let R := args[0]!; let vs := args[1]!; let r' := args[2]!; let r := args[3]!
    let viewTy := mkApp (mkConst ``Kraken.RegFile.View) R
    let vElems ← literalListElems vs
    let mut acc := #[]
    for idx in [0:vElems.size] do
      let v := vElems[idx]!
      let f := if v.isAppOfArity ``Kraken.RegFile.View.of 3 then v.getArg! 2
               else mkProj ``Kraken.RegFile.View 1 v
      let nm := match f.getAppFn.constName? with
        | some c => c.getString!
        | none => s!"view{idx}"
      let mem ← mkMemProof viewTy v vs idx
      let lhs := mkApp f r'
      let rhs := mkApp f r
      let prf ← mkExpectedTypeHint (mkApp2 h v mem) (← mkEq lhs rhs)
      acc := acc.push (nm, prf)
    return acc
  else
    return #[]

/-- Field/view equations of all `RegFile.EqExcept` and `RegFile.EqOn` hypotheses in context. -/
def frameEqsInContext : TacticM (Array Expr) := withMainContext do
  let mut acc := #[]
  for decl in (← getLCtx) do
    if decl.isImplementationDetail then continue
    let t := decl.type.consumeMData
    if t.isAppOf ``Kraken.RegFile.EqExcept || t.isAppOf ``Kraken.RegFile.EqOn then
      acc := acc ++ (← frameEqsOf decl.toExpr).map (·.2)
  return acc

/-- Try to prove `f r' = f r` from the field equations `eqs` of a frame hypothesis by unfolding `f`. -/
private def proveViewEq? (f r' r : Expr) (eqs : Array (String × Expr)) : TacticM (Option (Expr × Expr)) := do
  let some fName := f.getAppFn.constName? | return none
  let mainGoals ← getGoals
  let stmt ← mkEq (← mkAppM' f #[r']) (← mkAppM' f #[r])
  let g ← mkFreshExprMVar stmt
  let eqStx ← eqs.mapM fun (_, e) => do
    let t ← Term.exprToSyntax e
    `(Lean.Parser.Tactic.simpLemma| $t:term)
  let vId := mkIdent fName
  let closed ← do
    let s ← saveState
    try
      setGoals [g.mvarId!]
      evalTactic (← `(tactic| (simp only [$vId:ident, $eqStx,*]; done)))
      pure true
    catch _ => s.restore; pure false
  setGoals mainGoals
  if closed then
    return some (stmt, ← instantiateMVars g)
  else
    return none

/-! ### The `kframe_eqs` and `kframe` Tactics -/

/-- `kframe_eqs h [f, …]`: add the field/view equations `r'.f = r.f` of `h : r' ≡ r except W` or
`h : r' ≡ r on V` to the context (named `h_f`). Optional derived views `f : R → α` (such as a
multi-register projection) are added as `h_f : f r' = f r` when they only read preserved
registers (proved by unfolding `f` and rewriting with the field equations). -/
syntax (name := kframeEqs) "kframe_eqs " ident (" [" ident,* "]")? : tactic

elab_rules : tactic
  | `(tactic| kframe_eqs $h:ident $[[$views?:ident,*]]?) => withMainContext do
  let some decl := (← getLCtx).findFromUserName? h.getId
    | throwErrorAt h "unknown hypothesis `{h}`"
  let eqs ← frameEqsOf decl.toExpr
  if eqs.isEmpty then throwErrorAt h "`{h}` is not a `≡ … except` or `≡ … on` hypothesis"
  let mut hyps ← eqs.mapM fun (nm, prf) => do
    pure { userName := h.getId.appendAfter ("_" ++ nm), type := ← inferType prf, value := prf : Hypothesis }
  let hType := (← instantiateMVars decl.type).consumeMData
  let hArgs := hType.getAppArgs
  let r' := hArgs[hArgs.size - 2]!
  let r := hArgs[hArgs.size - 1]!
  -- For `EqExcept`, also derive equations for any unary view `f : R → α` occurring in the goal or
  -- local context that only reads preserved registers.
  if hType.isAppOfArity ``Kraken.RegFile.EqExcept 5 then
    let R := hArgs[0]!
    if let some rName := R.constName? then
      let candRef ← IO.mkRef (#[] : Array Name)
      let collectViews (e : Expr) : MetaM Unit := do
        e.forEach fun sub => do
          if let .app (.const c []) _ := sub then
            if !(`Kraken.RegFile).isPrefixOf c then
              let nm := c.getString!
              unless eqs.any (fun (n, _) => n == nm) || (← candRef.get).contains c do
                if let some cinfo := (← getEnv).find? c then
                  if let .forallE _ dom body _ := cinfo.type then
                    if dom.isConstOf rName && !body.isForall && body != mkSort .zero then
                      candRef.modify (·.push c)
      collectViews (← instantiateMVars (← getMainTarget))
      for d in (← getLCtx) do
        unless d.isImplementationDetail do
          collectViews (← instantiateMVars d.type)
      for c in (← candRef.get) do
        let nm := c.getString!
        if let some (stmt, value) ← proveViewEq? (mkConst c) r' r eqs then
          hyps := hyps.push { userName := h.getId.appendAfter ("_" ++ nm), type := stmt, value }
  if let some vs := views? then
    let vs : Array Ident := vs.getElems
    for v in vs do
      let nm := v.getId.getString!
      if hyps.any (fun hyp => hyp.userName == h.getId.appendAfter ("_" ++ nm)) then continue
      let f ← Term.elabTerm v none
      let f ← instantiateMVars f
      let some (stmt, value) ← proveViewEq? f r' r eqs
        | do
          let stmt ← mkEq (← mkAppM' f #[r']) (← mkAppM' f #[r])
          throwErrorAt v "kframe_eqs: `{v}` reads a register written by the block:{indentExpr stmt}"
      hyps := hyps.push { userName := h.getId.appendAfter ("_" ++ nm), type := stmt, value }
  let (_, g) ← (← getMainGoal).assertHypotheses hyps
  replaceMainGoal [g]

/-- Case-split a register name variable (allowing one level of nesting, e.g. `XRegOrSp.reg x`). -/
private partial def casesRegName (g : MVarId) (fvar : FVarId) : MetaM (List MVarId) := do
  let subgoals ← g.cases fvar
  subgoals.toList.flatMapM fun sg => do
    if h : sg.fields.size = 1 then
      let f := sg.fields[0]
      if f.isFVar then
        let ty ← sg.mvarId.withContext do whnfD (← inferType f)
        if let .const tyName _ := ty.getAppFn then
          if let some (.inductInfo info) := (← getEnv).find? tyName then
            if info.numIndices == 0 && !info.isRec then
              return ← casesRegName sg.mvarId f.fvarId!
    return [sg.mvarId]

/-- Prove a goal `r' ≡ r except W` or `r' ≡ r on V`:
- For `r' ≡ r except W`, each register not in `W` is closed by `rfl` or by rewriting with the
  frame equations of `≡ … except` / `≡ … on` hypotheses in the context; registers that cannot be
  closed are left as goals and reported in an info message (`kframe: add to writes: […]`).
- For `r' ≡ r on V`, each register or derived view in `V` is proved preserved by `rfl`, by
  rewriting with frame equations in the context, or by unfolding the view and rewriting. -/
elab "kframe" : tactic => withKrakenRecDepth <| withMainContext do
  evalTactic (← `(tactic| (try unfold Kraken.LoopAuto)))
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  if target.isAppOfArity ``Kraken.RegFile.EqOn 4 then
    if ← tryClose (← `(tactic| apply Kraken.RegFile.EqOn.refl)) then return
    let args := target.getAppArgs
    let vs := args[1]!; let r' := args[2]!; let r := args[3]!
    let vElems ← literalListElems vs
    let mut eqs ← frameEqsInContext
    for decl in (← getLCtx) do
      if decl.isImplementationDetail then continue
      let dt := (← instantiateMVars decl.type).consumeMData
      if dt.isAppOfArity ``Kraken.RegFile.EqExcept 5 then
        let hEqs ← frameEqsOf decl.toExpr
        let ra := dt.getArg! 3; let rb := dt.getArg! 4
        for v in vElems do
          if v.isAppOfArity ``Kraken.RegFile.View.of 3 then
            let f := v.getArg! 2
            if let some c := f.getAppFn.constName? then
              unless hEqs.any (fun (nm, _) => nm == c.getString!) do
                if let some (_, prf) ← proveViewEq? f ra rb hEqs then
                  eqs := eqs.push prf
    let eqStx ← eqs.mapM fun e => do
      let t ← Term.exprToSyntax e
      `(Lean.Parser.Tactic.simpLemma| $t:term)
    let mut cur ← getMainGoal
    let mut leaves : Array (Expr × MVarId) := #[]
    for v in vElems do
      let [gHead, gTail] ← cur.apply (mkConst ``Kraken.RegFile.EqOn.cons)
        | throwError "kframe: unexpected goals from `EqOn.cons`"
      let f := if v.isAppOfArity ``Kraken.RegFile.View.of 3 then v.getArg! 2
               else mkProj ``Kraken.RegFile.View 1 v
      let gHead ← gHead.replaceTargetDefEq (← mkEq (mkApp f r') (mkApp f r))
      leaves := leaves.push (f, gHead)
      cur := gTail
    discard <| cur.apply (mkConst ``Kraken.RegFile.EqOn.nil)
    let mut remaining := #[]
    for (f, leaf) in leaves do
      setGoals [leaf]
      if ← tryClose (← `(tactic| with_reducible rfl)) then continue
      if ← tryClose (← `(tactic| rfl)) then continue
      if !eqStx.isEmpty then
        if ← tryClose (← `(tactic| (simp only [$eqStx,*]; done))) then continue
        if ← tryClose (← `(tactic| (simp only [$eqStx,*]; rfl))) then continue
      if let some fName := f.getAppFn.constName? then
        let fId := mkIdent fName
        if ← tryClose (← `(tactic| (simp only [$fId:ident, $eqStx,*]; done))) then continue
        if ← tryClose (← `(tactic| (simp only [$fId:ident, $eqStx,*]; rfl))) then continue
      remaining := remaining.push leaf
    setGoals remaining.toList
    return
  unless target.isAppOfArity ``Kraken.RegFile.EqExcept 5 do
    throwError "kframe: expected a goal `r' ≡ r except W` or `r' ≡ r on V`, got{indentExpr target}"
  if ← tryClose (← `(tactic| apply Kraken.RegFile.EqExcept.refl)) then return
  let args := target.getAppArgs
  let R := args[0]!; let inst := args[1]!; let W := args[2]!
  let nameTy ← whnfD (mkApp2 (mkConst ``Kraken.RegFile.Name) R inst)
  let wElems ← literalListElems W
  let eqs ← frameEqsInContext
  let eqStx ← eqs.mapM fun e => do
    let t ← Term.exprToSyntax e
    `(Lean.Parser.Tactic.simpLemma| $t:term)
  let g ← getMainGoal
  let g ← g.replaceTargetDefEq (← whnfD target)
  let (fvars, g) ← g.introN 2 [`n, `hn]
  let leaves ← casesRegName g fvars[0]!
  let mut remaining := #[]
  let mut missingNames : Array String := #[]
  for leaf in leaves do
    setGoals [leaf]
    if ← tryClose (← `(tactic| with_reducible rfl)) then continue
    if ← tryClose (← `(tactic| rfl)) then continue
    let (n, hn, leaf) ← leaf.withContext do
      let t := (← instantiateMVars (← leaf.getType)).consumeMData
      let some (_, lhs, rhs) := t.eq? | throwError "kframe: unexpected goal{indentExpr t}"
      let n := lhs.getArg! 3
      let hn := (← getLCtx).decls.toList.filterMap id |>.reverse |>.find? fun (d : LocalDecl) =>
        d.type.consumeMData.isAppOf ``Not
      let leaf ← leaf.replaceTargetDefEq
        (← mkEq (← projFnApp (← whnfD lhs)) (← projFnApp (← whnfD rhs)))
      pure (n, hn, leaf)
    setGoals [leaf]
    if let some i ← findRegIdx? wElems n then
      let closed ← leaf.withContext do
        let some hnDecl := hn | pure false
        try
          let mem ← mkMemProof nameTy n W i
          let prf ← mkAppOptM ``absurd #[none, some (← leaf.getType), some mem, some hnDecl.toExpr]
          leaf.assign prf
          pure true
        catch _ => pure false
      if closed then continue
    if !eqStx.isEmpty then
      if ← tryClose (← `(tactic| (simp only [$eqStx,*]; done))) then continue
      if ← tryClose (← `(tactic| (simp only [$eqStx,*]; rfl))) then continue
    missingNames := missingNames.push (regNameString n)
    remaining := remaining.push leaf
  if !missingNames.isEmpty then
    logInfo m!"kframe: add to writes: [{String.intercalate ", " missingNames.toList}]"
  setGoals remaining.toList

end
