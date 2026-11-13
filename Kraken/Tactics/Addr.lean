module

public import Kraken.Layout
public import Kraken.Tactics.Util

/-!
# Program Layout Inspection and Address Normalization (`kaddr`)

Caching of program directive lengths and label indices (`ProgInfo`), label/position resolution,
and the `kaddr` tactic for discharging program-counter and label-offset equalities.
-/

public meta section

open Lean Meta Elab Tactic Kraken Kraken.Tactic

/-! ### Program Directive and Label Cache -/

structure ProgInfo where
  length : Nat
  labels : Std.HashMap String Nat := {}
  deriving Inhabited

private initialize progInfoCache : IO.Ref (NameMap ProgInfo) ← IO.mkRef {}

partial def extractDirectiveListElems (e : Expr) : MetaM (Array Expr) := do
  let mut cur := e
  let mut acc := #[]
  while true do
    if cur.isAppOfArity ``List.cons 3 then
      acc := acc.push (cur.getArg! 1)
      cur := cur.getArg! 2
    else if cur.isAppOfArity ``List.nil 1 then
      return acc
    else if let some unfolded ← unfoldDefinition? cur then
      cur := unfolded
    else
      throwError "kprologue: expected program to unfold to a literal list of directives"
  return acc

def getProgInfo? (declName : Name) : MetaM (Option ProgInfo) := do
  if let some info := (← progInfoCache.get).find? declName then
    return some info
  let some cinfo := (← getEnv).find? declName | return none
  let some val := cinfo.value? | return none
  let some elems ← (try some <$> extractDirectiveListElems val catch _ => pure none)
    | return none
  let mut labels : Std.HashMap String Nat := {}
  for h : i in [0:elems.size] do
    let d := elems[i]
    if d.getAppFn.constName?.map (·.getString!) == some "label" then
      if let some (.lit (.strVal lbl)) := d.getAppArgs.back? then
        unless labels.contains lbl do
          labels := labels.insert lbl i
  let info : ProgInfo := { length := elems.size, labels }
  progInfoCache.modify (·.insert declName info)
  return some info

def findLabelIdx (progIdent : Ident) (lbl : String) : TacticM Nat := do
  let declName ← resolveGlobalConstNoOverload progIdent
  let some info ← getProgInfo? declName
    | throwErrorAt progIdent "kprologue: `{declName}` has no directive list value"
  let some idx := info.labels[lbl]?
    | throwErrorAt progIdent "kprologue: label {repr lbl} not found in `{declName}`"
  return idx

def resolveDirectivePos (progIdent : Ident) (stx : TSyntax `term) :
    TacticM (TSyntax `term × Option Nat) := do
  if let some lbl := stx.raw.isStrLit? then
    let idx ← findLabelIdx progIdent lbl
    return (Syntax.mkNumLit (toString idx), some idx)
  else if let some idx := stx.raw.isNatLit? then
    return (stx, some idx)
  else
    return (stx, none)

/-- The program constant `p` of the first `(layout p)` occurring in `e`, if any. -/
def findLayoutProg? (e : Expr) : Option Name := do
  let sub ← e.find? fun s => s.isAppOfArity ``Kraken.Layout.apply 4 && s.appArg!.isConst
  return sub.appArg!.constName!

/-! ### The `kaddr` Tactic -/

/-- Discharge program address and label offset equalities for program(s) `ps`. -/
elab "kaddr" ps:ident+ : tactic => withKrakenRecDepth <| withMainContext do
  evalTactic (← `(tactic| (try unfold Kraken.LoopAuto)))
  let solved ← withReducible do
    try (← getMainGoal).refl; pure true catch _ => pure false
  if solved then return
  evalTactic (← `(tactic| (try simp only [Kraken.Executable.addrOf_zero, Kraken.Executable.startAddr_apply, Kraken.Layout.start_shift])))
  if (← getUnsolvedGoals).isEmpty then return
  let goal ← getMainGoal
  let cleanGoal ← clearSepAndLets goal
  replaceMainGoal [cleanGoal]
  let target0 ← instantiateMVars (← getMainTarget)
  let extraDeclsRef ← IO.mkRef (#[] : Array Ident)
  let hasShiftRef ← IO.mkRef false
  target0.forEach fun e => do
    if e.isAppOfArity ``List.length 2 then
      if let .const declName _ := e.appArg! then
        let extraDecls ← extraDeclsRef.get
        unless extraDecls.any (·.getId == declName) do
          extraDeclsRef.set (extraDecls.push (mkIdent declName))
    if e.isConstOf ``Kraken.Layout.shift then
      hasShiftRef.set true
  let extraDecls ← extraDeclsRef.get
  let hasShift ← hasShiftRef.get
  let allProgs := ps ++ extraDecls
  if !extraDecls.isEmpty || hasShift then
    let mut lenThms : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
    for p in allProgs do
      if let some declName ← (try some <$> resolveGlobalConstNoOverload p catch _ => pure none) then
        if let some info ← getProgInfo? declName then
          let pIdent := mkIdent declName
          let lenLit := Syntax.mkNumLit (toString info.length)
          lenThms := lenThms.push (← `(Lean.Parser.Tactic.simpLemma|
            Kraken.list_length_eq $pIdent $lenLit rfl))
    evalTactic (← `(tactic|
      (try simp only [Kraken.Layout.start_shift, Kraken.Layout.size_shift,
                      Nat.add_zero, Nat.zero_add, Nat.reduceAdd, $[$lenThms],*])))
    if (← getUnsolvedGoals).isEmpty then return
  let target ← instantiateMVars (← getMainTarget)
  let natLit? (e : Expr) : Option Nat :=
    if let some n := e.rawNatLit? then some n
    else if e.isAppOfArity ``OfNat.ofNat 3 then (e.getArg! 1).rawNatLit?
    else none
  let strLitsRef ← IO.mkRef (#[] : Array String)
  let sizeLitsRef ← IO.mkRef (#[] : Array Nat)
  let addrOfLitsRef ← IO.mkRef (#[] : Array Nat)
  target.forEach fun e => do
    if let .lit (.strVal s) := e then
      let strLits ← strLitsRef.get
      unless strLits.contains s do
        strLitsRef.set (strLits.push s)
    if e.isAppOfArity ``Kraken.Layout.size 4 then
      if let some n := natLit? e.appArg! then
        if n > 0 then
          let sizeLits ← sizeLitsRef.get
          unless sizeLits.contains n do
            sizeLitsRef.set (sizeLits.push n)
    if e.isAppOfArity ``Kraken.Executable.addrOf 4 then
      if let some n := natLit? e.appArg! then
        if n > 0 then
          let addrOfLits ← addrOfLitsRef.get
          unless addrOfLits.contains n do
            addrOfLitsRef.set (addrOfLits.push n)
  let strLits ← strLitsRef.get
  let sizeLits ← sizeLitsRef.get
  let addrOfLits ← addrOfLitsRef.get
  let mut simpThms : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
  for k in sizeLits do
    let kLit := Syntax.mkNumLit (toString k)
    let kSuccLit := Syntax.mkNumLit (toString (k + 1))
    simpThms := simpThms.push (← `(Lean.Parser.Tactic.simpLemma|
      Kraken.Layout.addrOf_add_size_eq _ $kLit $kSuccLit rfl))
  for p in allProgs do
    if let some declName ← (try some <$> resolveGlobalConstNoOverload p catch _ => pure none) then
      if let some info ← getProgInfo? declName then
        let pIdent := mkIdent declName
        unless addrOfLits.isEmpty do
          let lenLit := Syntax.mkNumLit (toString info.length)
          let hlenId := mkIdent (← mkFreshUserName `hlen)
          evalTactic (← `(tactic| have $hlenId : List.length $pIdent = $lenLit := rfl))
          for k in addrOfLits do
            if k ≤ info.length then
              let kLit := Syntax.mkNumLit (toString k)
              simpThms := simpThms.push (← `(Lean.Parser.Tactic.simpLemma|
                Kraken.Executable.addrOf_apply_of_length $hlenId $kLit rfl))
        for lbl in strLits do
          if let some idx := info.labels[lbl]? then
            let lblLit := Syntax.mkStrLit lbl
            let idxLit := Syntax.mkNumLit (toString idx)
            let hfindId := mkIdent (← mkFreshUserName `hfind)
            evalTactic (← `(tactic|
              have $hfindId : List.findIdx? (fun d => ArchDirective.label? d == some $lblLit) $pIdent = some $idxLit := rfl))
            simpThms := simpThms.push (← `(Lean.Parser.Tactic.simpLemma|
              Kraken.Executable.label_eq_layout_addrOf $pIdent $lblLit $idxLit $hfindId))
            simpThms := simpThms.push (← `(Lean.Parser.Tactic.simpLemma|
              Kraken.Executable.labels_label_eq_layout_addrOf $pIdent $lblLit $idxLit $hfindId))
  evalTactic (← `(tactic|
    (try simp only [Kraken.Executable.addrOf_zero, Kraken.Executable.startAddr_apply,
                    Kraken.Layout.start_shift, Kraken.Layout.size_shift,
                    Kraken.Layout.addrOf_zero, Kraken.Layout.start_add_size_zero,
                    Nat.add_zero, Nat.zero_add, Nat.reduceAdd,
                    $[$simpThms],*])))
  if (← getUnsolvedGoals).isEmpty then return
  for p in allProgs do
    evalTactic (← `(tactic| (try delta $p)))
  evalTactic (← `(tactic|
    ((try simp [Kraken.Executable.addrOf_zero, Kraken.Layout.apply, Kraken.Executable.addrOf,
                Kraken.Executable.sizeBefore, Kraken.Executable.withAddresses,
                Executable.labels, Kraken.Executable.labels, Kraken.Executable.label,
                Labels.label, ArchDirective.label?,
                List.mapIdx_cons, List.mapIdx_nil, Int64.ofNat_add, Int64.add_assoc]);
     (try grind))))

/-- Close the main goal (a program-counter equation) by `rfl` or `kaddr p`. -/
def closePcGoal (prog? : Option Name) : TacticM Bool := do
  if ← tryClose (← `(tactic| with_reducible rfl)) then return true
  if !(← instantiateMVars (← getMainTarget)).hasExprMVar then
    if ← tryClose (← `(tactic| rfl)) then return true
  match prog? with
  | some p => tryClose (← `(tactic| kaddr $(mkIdent p):ident))
  | none => pure false

end
