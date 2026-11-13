module

public import Kraken.Tactics.Util
public meta import Lean.Meta.Tactic.AC

/-!
# Separation Logic Cancellation and Memory Extraction (`ecancel`)

Binary tree representation of separating conjunctions (`SepTree`), $O(\text{depth})$ path
extraction (`extractSepTree`), congruence rebuilding (`rebuildSepTree`), byte-append and
take/drop slice expansion, `SepAtCandidate` extraction for `kstep`, and the `ecancel` tactic.
-/

public meta section

open Lean Elab Tactic Meta

namespace Kraken.Tactic

/-! ### Separation Trees and Path Extraction -/

private partial def denoteClauses (predType : Expr) : List Expr → MetaM Expr
  | [] => withLocalDeclD `m predType.bindingDomain! fun m => do
      let body ← mkAppM ``Std.ExtHashMap.emp #[m]
      mkLambdaFVars #[m] body (etaReduce := true)
  | [p] => return p
  | p :: ps => do
    let rest ← denoteClauses predType ps
    mkAppM ``Std.ExtHashMap.sep #[p, rest]

private partial def reduceProjectionApp (e : Expr) : MetaM Expr := do
  let e ← withConfig (fun c => { c with zetaDelta := false }) (whnfCore e.headBeta)
  let some declName := e.getAppFn.constName? | return e
  let some info ← getProjectionFnInfo? declName | return e
  if info.fromClass then
    unless declName == ``HasDataMem.dmem || declName == ``HasDataMem.withDmem do
      return e
    let some unfolded ← withTransparency .instances (unfoldProjInst? e) | return e
    return ← reduceProjectionApp unfolded.headBeta
  let args := e.getAppArgs
  if h : info.numParams < args.size then
    let major ← reduceProjectionApp args[info.numParams]
    let e := mkAppN e.getAppFn (args.set info.numParams major)
    let some unfolded ← unfoldDefinition? e | return e
    let some fn ← reduceProj? unfolded.getAppFn | return e
    reduceProjectionApp (mkAppN fn unfolded.getAppArgs)
  else
    return e

/-- Binary tree representation of a separating conjunction (`⋆` and `emp`). -/
inductive SepTree where
  | emp (e : Expr)
  | sep (e : Expr) (p q : SepTree)
  | atom (e : Expr)

def SepTree.toExpr : SepTree → Expr
  | .emp e | .sep e _ _ | .atom e => e

def SepTree.numClauses : SepTree → Nat
  | .emp _ => 0
  | .sep _ p q => p.numClauses + q.numClauses
  | .atom _ => 1

def SepTree.clauses : SepTree → List Expr
  | .emp _ => []
  | .sep _ p q => p.clauses ++ q.clauses
  | .atom e => [e]

partial def parseSepTree (e : Expr) : MetaM SepTree := do
  let e ← reduceProjectionApp (← instantiateMVars e)
  if e.getAppFn.constName? == some ``Std.ExtHashMap.emp then
    return .emp e
  if e.getAppFn.constName? == some ``Std.ExtHashMap.sep then
    let args := e.getAppArgs
    let p ← parseSepTree args[args.size - 2]!
    let q ← parseSepTree args[args.size - 1]!
    return .sep e p q
  return .atom e

private inductive LeafExtract where
  | single (a : Expr) (h : Expr)
  | split (a : Expr) (rem : Expr) (h : Expr)

private partial def extractSepTreeAux (t : SepTree) (targetIdx : Nat)
    (atLeaf : Expr → MetaM LeafExtract) : MetaM (Option LeafExtract) := do
  match t with
  | .emp _ => return none
  | .atom e =>
    if targetIdx == 0 then
      return some (← atLeaf e)
    else
      return none
  | .sep _ p q =>
    let pCount := p.numClauses
    if targetIdx < pCount then
      let some res ← extractSepTreeAux p targetIdx atLeaf | return none
      match res with
      | .single a hp =>
        let h ← mkAppM ``Std.ExtHashMap.sep_extract_head #[q.toExpr, hp]
        return some (.split a q.toExpr h)
      | .split a p' hp =>
        let rem ← mkAppM ``Std.ExtHashMap.sep #[p', q.toExpr]
        let h ← mkAppM ``Std.ExtHashMap.sep_extract_left #[q.toExpr, hp]
        return some (.split a rem h)
    else
      let some res ← extractSepTreeAux q (targetIdx - pCount) atLeaf | return none
      match res with
      | .single a hq =>
        let h ← mkAppM ``Std.ExtHashMap.sep_extract_tail #[p.toExpr, hq]
        return some (.split a p.toExpr h)
      | .split a q' hq =>
        let rem ← mkAppM ``Std.ExtHashMap.sep #[p.toExpr, q']
        let h ← mkAppM ``Std.ExtHashMap.sep_extract_right #[p.toExpr, hq]
        return some (.split a rem h)

/-- Extract (or split and extract) the leaf at `targetIdx` from `t` along the binary tree path
in $O(\text{depth})$ steps. Returns `(extractedClause, frameExpr, eqProof)` where
`eqProof : t.toExpr = extractedClause ⋆ frameExpr`. -/
private def extractSepTree (t : SepTree) (targetIdx : Nat)
    (atLeaf : Expr → MetaM LeafExtract) : MetaM (Option (Expr × Expr × Expr)) := do
  let some res ← extractSepTreeAux t targetIdx atLeaf | return none
  match res with
  | .split a frame h => return some (a, frame, h)
  | .single a h =>
    let h' ← mkAppM ``Std.ExtHashMap.sep_extract_here #[h]
    let eqType ← inferType h'
    let frame := eqType.appArg!.appArg!
    return some (a, frame, h')

/-- Lift optional equality proofs on `p` and `q` through `Std.ExtHashMap.sep`. -/
private def mkSepCongr (p' q' : Expr) (hp? hq? : Option Expr) :
    MetaM (Expr × Option Expr) := do
  let sep' ← mkAppM ``Std.ExtHashMap.sep #[p', q']
  let hSep? ← match hp?, hq? with
    | none, none => pure none
    | some hp, none =>
      let h1 ← mkCongrArg sep'.appFn!.appFn! hp
      some <$> mkCongrFun h1 q'
    | none, some hq =>
      some <$> mkCongrArg sep'.appFn! hq
    | some hp, some hq =>
      let h1 ← mkCongrArg sep'.appFn!.appFn! hp
      some <$> mkCongr h1 hq
  return (sep', hSep?)

/-- Rebuild a separation predicate from its parsed `SepTree` while replacing each atomic leaf,
from left to right, with the next entry in `clauses`. -/
private partial def rebuildSepTree (t : SepTree) (clauses : List (Expr × Option Expr)) :
    MetaM (Option (Expr × Option Expr × List (Expr × Option Expr))) := do
  match t with
  | .emp e => return some (e, none, clauses)
  | .sep _ p q =>
    let some (p', hp?, clauses) ← rebuildSepTree p clauses | return none
    let some (q', hq?, clauses) ← rebuildSepTree q clauses | return none
    let (sep', hSep?) ← mkSepCongr p' q' hp? hq?
    return some (sep', hSep?, clauses)
  | .atom e =>
    if let .mvar mvarId := e then
      if ← mvarId.isAssigned then
        return ← rebuildSepTree (← parseSepTree e) clauses
    match clauses with
    | (c, eqProof?) :: rest => return some (← instantiateMVars c, eqProof?, rest)
    | [] => return none

/-! ### Atomic Matching and Propositional `At` Congruence -/

private def shouldNotUnfoldInMatchClosed (fn : Expr) : Bool :=
  match fn.constName? with
  | some n =>
    n == ``Int.toBytes || n == ``Int.ofBytes ||
    n == ``Nat.toBytes || n == ``Nat.ofBytes ||
    (`BitVec).isPrefixOf n || (`List).isPrefixOf n ||
    (`HAdd).isPrefixOf n || (`Add).isPrefixOf n ||
    (`HSub).isPrefixOf n || (`Sub).isPrefixOf n ||
    (`HAppend).isPrefixOf n || (`Append).isPrefixOf n
  | none => false

/-- Bounded definitional matching for separation clauses without unfolding arithmetic or byte
conversions. -/
private partial def matchClosed (lhs rhs : Expr) (fuel : Nat := 2) : MetaM Bool := do
  let lhs ← instantiateMVars lhs
  let rhs ← instantiateMVars rhs
  if lhs == rhs then return true
  if lhs.isMVar || rhs.isMVar then return ← isDefEq lhs rhs
  let lhs ← reduceProjectionApp lhs
  let rhs ← reduceProjectionApp rhs
  if lhs == rhs then return true
  if !lhs.hasFVar && !rhs.hasFVar && !lhs.hasExprMVar && !rhs.hasExprMVar then
    return ← isDefEq lhs rhs
  if lhs.isFVar then
    if let some val ← lhs.fvarId!.getValue? then
      return ← matchClosed val rhs fuel
  if rhs.isFVar then
    if let some val ← rhs.fvarId!.getValue? then
      return ← matchClosed lhs val fuel
  if lhs.getAppFn == rhs.getAppFn then
    let lhsArgs := lhs.getAppArgs
    let rhsArgs := rhs.getAppArgs
    unless lhsArgs.size == rhsArgs.size do return false
    for lhsArg in lhsArgs, rhsArg in rhsArgs do
      unless ← matchClosed lhsArg rhsArg fuel do return false
    return true
  if fuel == 0 then
    return false
  unless shouldNotUnfoldInMatchClosed lhs.getAppFn do
    if let some lhs ← unfoldDefinition? lhs then
      if ← matchClosed lhs rhs (fuel - 1) then return true
  unless shouldNotUnfoldInMatchClosed rhs.getAppFn do
    if let some rhs ← unfoldDefinition? rhs then
      if ← matchClosed lhs rhs (fuel - 1) then return true
  return false

private def matchAtom (lhs rhs : Expr) : MetaM Bool := do
  if lhs.hasExprMVar || rhs.hasExprMVar then
    commitWhen (matchClosed lhs rhs)
  else
    matchClosed lhs rhs

/-- Extract `(bs, addr)` from a memory clause `Eq (bs.At addr)` (normalising `UInt*.At` to
`UInt*.toBytes.At`). -/
def extractAtBytesAndAddr? (clause : Expr) : MetaM (Option (Expr × Expr)) := do
  let clause ← instantiateMVars clause
  unless clause.isAppOfArity ``Eq 2 do return none
  let rhs ← reduceProjectionApp clause.appArg!
  if rhs.isAppOfArity ``List.At 3 then
    return some (← reduceProjectionApp rhs.appFn!.appArg!, ← reduceProjectionApp rhs.appArg!)
  if rhs.isAppOfArity ``UInt64.At 3 then
    let v ← reduceProjectionApp rhs.appFn!.appArg!
    return some (← mkAppM ``UInt64.toBytes #[v], ← reduceProjectionApp rhs.appArg!)
  if rhs.isAppOfArity ``UInt32.At 3 then
    let v ← reduceProjectionApp rhs.appFn!.appArg!
    return some (← mkAppM ``UInt32.toBytes #[v], ← reduceProjectionApp rhs.appArg!)
  if rhs.isAppOfArity ``UInt16.At 3 then
    let v ← reduceProjectionApp rhs.appFn!.appArg!
    return some (← mkAppM ``UInt16.toBytes #[v], ← reduceProjectionApp rhs.appArg!)
  if rhs.isAppOfArity ``UInt8.At 3 then
    let v ← reduceProjectionApp rhs.appFn!.appArg!
    return some (← mkAppM ``UInt8.toBytes #[v], ← reduceProjectionApp rhs.appArg!)
  return none

/-- Lift `hBs : bs₁ = bs₂` to `Eq (bs₁.At addr) = Eq (bs₂.At addr)`. -/
private def mkEqAtBsCongr (bs₁ addr hBs : Expr) : MetaM Expr := do
  let fn ← withLocalDeclD `bs (← inferType bs₁) fun bs => do
    let atExpr ← mkAppM ``List.At #[bs, addr]
    let eqExpr ← mkAppM ``Eq #[atExpr]
    mkLambdaFVars #[bs] eqExpr
  mkCongrArg fn hBs

/-- Lift `hAddr : addr₁ = addr₂` to `Eq (bs.At addr₁) = Eq (bs.At addr₂)`. -/
private def mkEqAtAddrCongr (bs addr₁ hAddr : Expr) : MetaM Expr := do
  let fn ← withLocalDeclD `a (← inferType addr₁) fun a => do
    let atExpr ← mkAppM ``List.At #[bs, a]
    let eqExpr ← mkAppM ``Eq #[atExpr]
    mkLambdaFVars #[a] eqExpr
  mkCongrArg fn hAddr

private def matchPropAt (lhs rhs : Expr) : MetaM (Option Expr) := do
  let some (bs₁, addr₁) ← extractAtBytesAndAddr? lhs | return none
  let some (bs₂, addr₂) ← extractAtBytesAndAddr? rhs | return none
  if ← matchClosed addr₁ addr₂ then
    let some hBs ← provePropEq bs₁ bs₂ | return none
    return some (← mkEqAtBsCongr bs₁ addr₁ hBs)
  if ← matchClosed bs₁ bs₂ then
    let some hAddr ← provePropEq addr₁ addr₂ | return none
    return some (← mkEqAtAddrCongr bs₁ addr₁ hAddr)
  let some hAddr ← provePropEq addr₁ addr₂ | return none
  let some hBs ← provePropEq bs₁ bs₂ | return none
  let h1 ← mkEqAtBsCongr bs₁ addr₁ hBs
  let h2 ← mkEqAtAddrCongr bs₂ addr₁ hAddr
  return some (← mkEqTrans h1 h2)

/-! ### Slot Alignment and Cancellation -/

private def isNakedMVar : Expr → Bool
  | .mvar _ => true
  | _ => false

private inductive ClauseSlot where
  | unmatched (e : Expr)
  | matched (c : Expr) (eqProof? : Option Expr := none)
  deriving Inhabited

private abbrev ClauseSlots := Array ClauseSlot

private def unmatchedIndices (slots : ClauseSlots) : List (Nat × Expr) := Id.run do
  let mut res := []
  for h : i in [0:slots.size] do
    if let .unmatched e := slots[i] then
      res := res ++ [(i, e)]
  return res

private def instantiateSlotMVars (slots : ClauseSlots) : MetaM ClauseSlots :=
  slots.mapM fun
    | .unmatched e => return .unmatched (← instantiateMVars e)
    | .matched c eqProof? => return .matched (← instantiateMVars c) eqProof?

private def extractCanonical (slots : ClauseSlots) :
    Option (List (Expr × Option Expr)) := Id.run do
  let mut res := []
  for s in slots do
    match s with
    | .unmatched _ => return none
    | .matched c eqProof? => res := res ++ [(c, eqProof?)]
  return some res

private def spliceAt (slots : ClauseSlots) (idx : Nat) (replacement : List Expr) :
    List (Expr × Option Expr) := Id.run do
  let mut res := []
  for h : i in [0:slots.size] do
    if i == idx then
      res := res ++ replacement.map (·, none)
    else if let .matched c eqProof? := slots[i] then
      res := res ++ [(c, eqProof?)]
  return res

private def tryAssignNakedSlot (predType : Expr) (lhs rhs : ClauseSlots) :
    MetaM (Option (List (Expr × Option Expr) × List (Expr × Option Expr))) := do
  match unmatchedIndices lhs, unmatchedIndices rhs with
  | [(i, .mvar mvarId)], remRhsPairs =>
    let remRhs := remRhsPairs.map Prod.snd
    unless ← isDefEq (.mvar mvarId) (← denoteClauses predType remRhs) do return none
    let rhs' := rhs.map fun | .unmatched r => .matched r none | .matched c eq? => .matched c eq?
    let some rhsCan := extractCanonical rhs' | return none
    let lhsCan := spliceAt lhs i remRhs
    return some (lhsCan, rhsCan)
  | remLhsPairs, [(j, .mvar mvarId)] =>
    let remLhs := remLhsPairs.map Prod.snd
    unless ← isDefEq (.mvar mvarId) (← denoteClauses predType remLhs) do return none
    let lhs' := lhs.map fun | .unmatched l => .matched l none | .matched c eq? => .matched c eq?
    let some lhsCan := extractCanonical lhs' | return none
    let rhsCan := spliceAt rhs j remLhs
    return some (lhsCan, rhsCan)
  | _, _ => return none

/-- Greedily cancel closed clauses in a single pass while recording their canonical alignment. -/
private def cancelClosedSlots (lhs rhs : ClauseSlots) : MetaM (ClauseSlots × ClauseSlots) := do
  let mut lhs := lhs
  let mut rhs := rhs
  for i in [0:lhs.size] do
    if let .unmatched l := lhs[i]! then
      if !l.hasExprMVar then
        let mut matchedIdx? : Option Nat := none
        for j in [0:rhs.size] do
          if matchedIdx?.isNone then
            if let .unmatched r := rhs[j]! then
              if !r.hasExprMVar then
                if ← matchClosed l r then
                  matchedIdx? := some j
        if let some j := matchedIdx? then
          lhs := lhs.set! i (.matched l)
          rhs := rhs.set! j (.matched l)
  return (lhs, rhs)

/-- Match remaining closed `At` clauses whose addresses or byte values are propositionally equal. -/
private def cancelPropAtSlots (lhs rhs : ClauseSlots) : MetaM (ClauseSlots × ClauseSlots) := do
  let mut lhs := lhs
  let mut rhs := rhs
  for i in [0:lhs.size] do
    if let .unmatched l := lhs[i]! then
      if !l.hasExprMVar then
        let mut matched? : Option (Nat × Expr) := none
        for j in [0:rhs.size] do
          if matched?.isNone then
            if let .unmatched r := rhs[j]! then
              if !r.hasExprMVar then
                if let some eqPrf ← matchPropAt l r then
                  matched? := some (j, eqPrf)
        if let some (j, eqPrf) := matched? then
          lhs := lhs.set! i (.matched l none)
          rhs := rhs.set! j (.matched l (some eqPrf))
  return (lhs, rhs)

private partial def cancelAndAlign (predType : Expr) (lhs rhs : ClauseSlots) :
    MetaM (Option (List (Expr × Option Expr) × List (Expr × Option Expr))) := do
  let (lhs, rhs) ← cancelClosedSlots lhs rhs
  if let (some lhsCan, some rhsCan) := (extractCanonical lhs, extractCanonical rhs) then
    return some (lhsCan, rhsCan)
  for i in [0:lhs.size] do
    if let .unmatched l := lhs[i]! then
      for j in [0:rhs.size] do
        if let .unmatched r := rhs[j]! then
          if (l.hasExprMVar || r.hasExprMVar) && !isNakedMVar l && !isNakedMVar r then
            let res? ← commitWhenSomeNoEx? do
              unless ← matchAtom l r do return none
              let c ← instantiateMVars l
              let lhs' ← instantiateSlotMVars (lhs.set! i (.matched c))
              let rhs' ← instantiateSlotMVars (rhs.set! j (.matched c))
              cancelAndAlign predType lhs' rhs'
            if res?.isSome then return res?
  let (lhs, rhs) ← cancelPropAtSlots lhs rhs
  if let (some lhsCan, some rhsCan) := (extractCanonical lhs, extractCanonical rhs) then
    return some (lhsCan, rhsCan)
  tryAssignNakedSlot predType lhs rhs

/-! ### Byte Append and Slice Splitting -/

private def extractListAppendArgs? (e : Expr) : Option (Expr × Expr) :=
  if e.isAppOfArity ``HAppend.hAppend 6 then
    let args := e.getAppArgs
    some (args[4]!, args[5]!)
  else if e.isAppOfArity ``List.append 3 then
    let args := e.getAppArgs
    some (args[1]!, args[2]!)
  else
    none

private def inferKnownByteLength? (bs : Expr) : MetaM (Option (Expr × Expr)) := do
  let bs ← instantiateMVars bs
  if bs.isAppOfArity ``Int.toBytes 2 then
    let n := bs.appFn!.appArg!
    let v := bs.appArg!
    return some (n, ← mkAppM ``Int.toBytes_length #[n, v])
  if bs.isAppOfArity ``Nat.toBytes 2 then
    let n := bs.appFn!.appArg!
    let v := bs.appArg!
    return some (n, ← mkAppM ``Nat.toBytes_length #[n, v])
  for localDecl? in (← getLCtx).decls.toArray.reverse do
    if let some localDecl := localDecl? then
      let t ← instantiateMVars localDecl.type
      if t.isAppOfArity ``Eq 3 then
        let lhs := t.appFn!.appArg!
        let rhs := t.appArg!
        if lhs.isAppOfArity ``List.length 2 && lhs.appArg! == bs then
          return some (rhs, localDecl.toExpr)
  return none

private partial def expandAppendsInSepExpr (e : Expr) (fuel : Nat := 4) : MetaM (Expr × Option Expr) := do
  if fuel == 0 then
    return (e, none)
  let e ← reduceProjectionApp (← instantiateMVars e)
  if e.getAppFn.constName? == some ``Std.ExtHashMap.sep then
    let args := e.getAppArgs
    let p := args[args.size - 2]!
    let q := args[args.size - 1]!
    let (p', hp?) ← expandAppendsInSepExpr p fuel
    let (q', hq?) ← expandAppendsInSepExpr q fuel
    if hp?.isNone && hq?.isNone then
      return (e, none)
    return ← mkSepCongr p' q' hp? hq?
  let some (bs, a) ← extractAtBytesAndAddr? e | return (e, none)
  if bs.hasExprMVar || a.hasExprMVar then
    return (e, none)
  let some (bs1, bs2) := extractListAppendArgs? bs | return (e, none)
  let splitRes? ← commitWhenSomeNoEx? do
    let len1? ← inferKnownByteLength? bs1
    let len2? ← inferKnownByteLength? bs2
    let hSplit ← match len1?, len2? with
      | some (n1, hN1), some (n2, hN2) =>
        let splitFn ← mkAppM ``Mem.At_append_sep_len2 #[bs1, bs2, n1, n2, a, hN1, hN2]
        let lenBoundType := (← inferType splitFn).bindingDomain!
        let some hLen ← provePropGoal lenBoundType | return none
        pure (mkApp splitFn hLen)
      | some (n1, hN1), none =>
        let splitFn ← mkAppM ``Mem.At_append_sep_len #[bs1, bs2, n1, a, hN1]
        let lenBoundType := (← inferType splitFn).bindingDomain!
        let some hLen ← provePropGoal lenBoundType | return none
        pure (mkApp splitFn hLen)
      | none, _ =>
        let splitFn ← mkAppM ``Mem.At_append_sep #[bs1, bs2, a]
        let lenBoundType := (← inferType splitFn).bindingDomain!
        let some hLen ← provePropGoal lenBoundType | return none
        pure (mkApp splitFn hLen)
    let actualLhs := (← inferType hSplit).appFn!.appArg!
    if e == actualLhs then
      return some hSplit
    else
      return some (← mkExpectedTypeHint hSplit (← mkEq e (← inferType hSplit).appArg!))
  let some hSplit := splitRes? | return (e, none)
  let splitRhs := (← inferType hSplit).appArg!
  let (splitRhs', hMore?) ← expandAppendsInSepExpr splitRhs (fuel - 1)
  let hTotal ← match hMore? with
    | none => pure hSplit
    | some hMore => mkEqTrans hSplit hMore
  return (splitRhs', some hTotal)

private def collectTakeTargets (clauses : List Expr) : MetaM (Array (Expr × Expr)) := do
  let mut res := #[]
  for clause in clauses do
    if let some (bsExpr, _) ← extractAtBytesAndAddr? clause then
      if bsExpr.isAppOfArity ``List.take 3 then
        let k := bsExpr.appFn!.appArg!
        let bs' := bsExpr.appArg!
        unless res.any (fun (b, n) => b == bs' && n == k) do
          res := res.push (bs', k)
  return res

private partial def expandSlicesInSepExpr (e : Expr) (takeTargets : Array (Expr × Expr))
    (fuel : Nat := 4) : MetaM (Expr × Option Expr) := do
  if fuel == 0 || takeTargets.isEmpty then
    return (e, none)
  let e ← reduceProjectionApp (← instantiateMVars e)
  if e.getAppFn.constName? == some ``Std.ExtHashMap.sep then
    let args := e.getAppArgs
    let p := args[args.size - 2]!
    let q := args[args.size - 1]!
    let (p', hp?) ← expandSlicesInSepExpr p takeTargets fuel
    let (q', hq?) ← expandSlicesInSepExpr q takeTargets fuel
    if hp?.isNone && hq?.isNone then
      return (e, none)
    return ← mkSepCongr p' q' hp? hq?
  let some (bs, a) ← extractAtBytesAndAddr? e | return (e, none)
  if bs.hasExprMVar || a.hasExprMVar then
    return (e, none)
  for (bs', k) in takeTargets do
    let matchRes? ← commitWhenSomeNoEx? do
      let (bsTarget, hBs?) ←
        if ← matchClosed bs bs' then
          pure (bs, none)
        else if bs.isAppOfArity ``List.drop 3 && bs'.isAppOfArity ``List.drop 3 then
          let some hBs ← provePropEq bs bs' | return none
          pure (bs', some hBs)
        else
          return none
      let splitFn ← mkAppM ``Mem.At_take_drop_sep #[bsTarget, k, a]
      let splitFnType ← inferType splitFn
      let kType := splitFnType.bindingDomain!
      let lenBoundType := splitFnType.bindingBody!.bindingDomain!
      let some hK ← provePropGoal kType | return none
      let some hLen ← provePropGoal lenBoundType | return none
      let hSplit := mkApp2 splitFn hK hLen
      let hSplit ← match hBs? with
        | none =>
          let actualLhs := (← inferType hSplit).appFn!.appArg!
          if e == actualLhs then
            pure hSplit
          else
            mkExpectedTypeHint hSplit (← mkEq e (← inferType hSplit).appArg!)
        | some hBs =>
          let hCongr ← mkEqAtBsCongr bs a hBs
          mkEqTrans hCongr hSplit
      return some hSplit
    if let some hSplit := matchRes? then
      let splitRhs := (← inferType hSplit).appArg!
      let (splitRhs', hMore?) ← expandSlicesInSepExpr splitRhs takeTargets (fuel - 1)
      let hTotal ← match hMore? with
        | none => pure hSplit
        | some hMore => mkEqTrans hSplit hMore
      return (splitRhs', some hTotal)
  return (e, none)

/-! ### Separation Equality and Hypothesis Solvers -/

private def solveSepEqCore (lhs rhs : Expr) : MetaM (Option Expr) :=
  commitWhenSomeNoEx? do
    let lhs ← instantiateMVars lhs
    let rhs ← instantiateMVars rhs
    if lhs == rhs then
      return some (← mkEqRefl lhs)
    let predType ← inferType lhs
    let lhsTree ← parseSepTree lhs
    let rhsTree ← parseSepTree rhs
    let lhsSlots := lhsTree.clauses.toArray.map ClauseSlot.unmatched
    let rhsSlots := rhsTree.clauses.toArray.map ClauseSlot.unmatched
    if !lhs.hasExprMVar && !rhs.hasExprMVar && lhsSlots.size != rhsSlots.size then
      return none
    let some (lhsCan, rhsCan) ← cancelAndAlign predType lhsSlots rhsSlots | return none
    let some (lhs', _, []) ← rebuildSepTree lhsTree lhsCan | return none
    let some (rhs', rhsEq?, []) ← rebuildSepTree rhsTree rhsCan | return none
    let acProof ← mkFreshExprMVar (← mkEq lhs' rhs')
    Lean.Meta.AC.rewriteUnnormalizedRefl acProof.mvarId!
    let acProof ← instantiateMVars acProof
    match rhsEq? with
    | some rhsEq => return some (← mkEqTrans acProof rhsEq)
    | none => return some acProof

private def chainOptEq (h1? h2? : Option Expr) : MetaM (Option Expr) := do
  match h1?, h2? with
  | none, none => return none
  | some h1, none => return some h1
  | none, some h2 => return some h2
  | some h1, some h2 => return some (← mkEqTrans h1 h2)

private def solveSepEq (lhs rhs : Expr) : MetaM (Option Expr) := do
  if let some prf ← solveSepEqCore lhs rhs then
    return some prf
  commitWhenSomeNoEx? do
    let lhs ← instantiateMVars lhs
    let rhs ← instantiateMVars rhs
    let (lhs1, hLhs1?) ← expandAppendsInSepExpr lhs
    let (rhs1, hRhs1?) ← expandAppendsInSepExpr rhs
    let lhsTree ← parseSepTree lhs1
    let rhsTree ← parseSepTree rhs1
    let rhsTakes ← collectTakeTargets rhsTree.clauses
    let lhsTakes ← collectTakeTargets lhsTree.clauses
    let (lhs2, hLhs2?) ← expandSlicesInSepExpr lhs1 rhsTakes
    let (rhs2, hRhs2?) ← expandSlicesInSepExpr rhs1 lhsTakes
    let hLhs? ← chainOptEq hLhs1? hLhs2?
    let hRhs? ← chainOptEq hRhs1? hRhs2?
    if hLhs?.isNone && hRhs?.isNone then
      return none
    let some hMid ← solveSepEqCore lhs2 rhs2 | return none
    let hMid ← match hLhs? with
      | some hLhs => mkEqTrans hLhs hMid
      | none => pure hMid
    let hMid ← match hRhs? with
      | some hRhs => mkEqTrans hMid (← mkEqSymm hRhs)
      | none => pure hMid
    return some hMid

private def solveFromHypothesis (target : Expr) (localDecl : LocalDecl) : MetaM (Option Expr) := do
  let hypType ← reduceProjectionApp (← instantiateMVars localDecl.type)
  unless target.isApp && hypType.isApp do return none
  let targetFn := target.appFn!
  let targetArg := target.appArg!
  let hypFn := hypType.appFn!
  let hypArg := hypType.appArg!
  unless ← matchAtom (← reduceProjectionApp targetArg) (← reduceProjectionApp hypArg) do
    return none
  let some hSeps ← solveSepEq hypFn targetFn | return none
  let hFunEq ← mkAppM ``congrFun #[hSeps, hypArg]
  return some (← mkAppM ``Eq.mp #[hFunEq, localDecl.toExpr])

/-! ### Direct `At`-Candidate Extraction for Symbolic Execution -/

structure SepAtCandidate where
  hyp : Expr
  hypArg : Expr
  hypTree : SepTree
  clause : Expr
  clauseIdx : Nat
  bs : Expr
  addr : Expr

/-- Given a separation-logic subgoal `P m` of the form `(Eq (?bs.At ?addr') ⋆ ?R) s.dmem`,
search the local context from newest to oldest for hypotheses `Q m'` where `m'` matches `m`,
parse `Q` once into a `SepTree`, and return all `At` clause candidates. -/
def findSepAtCandidates (starGoal : MVarId) : MetaM (Array SepAtCandidate) := starGoal.withContext do
  let target ← reduceProjectionApp (← instantiateMVars (← starGoal.getType))
  unless target.isApp do return #[]
  let targetArg ← reduceProjectionApp target.appArg!
  let mut cands := #[]
  for localDecl? in (← getLCtx).decls.toArray.reverse do
    if let some localDecl := localDecl? then
      let hypType ← reduceProjectionApp (← instantiateMVars localDecl.type)
      if hypType.isApp then
        let hypFn := hypType.appFn!
        let hypArg := hypType.appArg!
        if ← matchAtom targetArg (← reduceProjectionApp hypArg) then
          let hypTree ← parseSepTree hypFn
          let clauses := hypTree.clauses
          for h : idx in [0:clauses.length] do
            let clause := clauses[idx]
            if let some (bs, addr) ← extractAtBytesAndAddr? clause then
              cands := cands.push {
                hyp := localDecl.toExpr
                hypArg
                hypTree
                clause
                clauseIdx := idx
                bs
                addr
              }
  return cands

/-- Directly solve a `starGoal` of the form `(Eq (?bs.At ?addr') ⋆ ?R) s.dmem` using a
pre-matched `SepAtCandidate` by extracting (or splitting and extracting via `leafSplit?`)
the target leaf along the binary tree path in $O(\text{depth})$ steps. -/
def solveSepAtCandidate (starGoal : MVarId) (cand : SepAtCandidate)
    (leafSplit? : Option Expr := none) : MetaM Bool :=
  starGoal.withContext do
    withConfig (fun config => { config with assignSyntheticOpaque := true }) do
      let res? ← commitWhenSomeNoEx? do
        let target ← reduceProjectionApp (← instantiateMVars (← starGoal.getType))
        unless target.isApp do return none
        let targetFn := target.appFn!
        let sepArgs := targetFn.getAppArgs
        unless sepArgs.size >= 2 do return none
        let atClause := sepArgs[sepArgs.size - 2]!
        let rMVar := sepArgs[sepArgs.size - 1]!
        unless atClause.isAppOfArity ``Eq 2 do return none
        let atExpr := atClause.appArg!
        unless atExpr.isAppOfArity ``List.At 3 do return none
        let bsMVar := atExpr.appFn!.appArg!
        let addrMVar := atExpr.appArg!
        let hSeps ← match leafSplit? with
          | none =>
            unless ← isDefEq addrMVar cand.addr do return none
            unless ← isDefEq bsMVar cand.bs do return none
            let atClause ← instantiateMVars atClause
            let hRefl ← mkEqRefl atClause
            let hLeaf ←
              if cand.clause == atClause then
                pure hRefl
              else
                mkExpectedTypeHint hRefl (← mkEq cand.clause atClause)
            let some (_, frameExpr, hSeps) ←
              extractSepTree cand.hypTree cand.clauseIdx (fun _ => return .single atClause hLeaf)
              | return none
            unless ← isDefEq rMVar frameExpr do return none
            pure hSeps
          | some hSplit =>
            let splitEqType ← instantiateMVars (← inferType hSplit)
            unless splitEqType.isAppOfArity ``Eq 3 do return none
            let splitRhs := splitEqType.appArg!
            let splitRhsArgs := splitRhs.getAppArgs
            unless splitRhsArgs.size >= 2 do return none
            let extractedClause := splitRhsArgs[splitRhsArgs.size - 2]!
            let remainderClause := splitRhsArgs[splitRhsArgs.size - 1]!
            let some (splitBs, splitAddr) ← extractAtBytesAndAddr? extractedClause | return none
            unless ← isDefEq addrMVar splitAddr do return none
            unless ← isDefEq bsMVar splitBs do return none
            let atClause ← instantiateMVars atClause
            let hSplit ←
              if cand.clause == splitEqType.appFn!.appArg! && extractedClause == atClause then
                pure hSplit
              else
                let expectedSplit ← mkEq cand.clause (← mkAppM ``Std.ExtHashMap.sep #[atClause, remainderClause])
                mkExpectedTypeHint hSplit expectedSplit
            let some (_, frameExpr, hSeps) ←
              extractSepTree cand.hypTree cand.clauseIdx
                (fun _ => return .split atClause remainderClause hSplit)
              | return none
            unless ← isDefEq rMVar frameExpr do return none
            pure hSeps
        let hFunEq ← mkAppM ``congrFun #[hSeps, cand.hypArg]
        let proof ← mkAppM ``Eq.mp #[hFunEq, cand.hyp]
        starGoal.assign proof
        return some ()
      return res?.isSome

/-! ### The `ecancel` Tactic -/

/-- Discharge a separation-logic equality `P = Q` or hypothesis entailment `P m` by matching
and cancelling atomic clauses (with automatic byte-append and slice splitting). -/
def ecancelGoal (goal : MVarId) : MetaM Bool := goal.withContext do
  let target ← reduceProjectionApp (← instantiateMVars (← goal.getType))
  withConfig (fun config => { config with assignSyntheticOpaque := true }) do
    if target.isAppOfArity ``Eq 3 then
      let args := target.getAppArgs
      if let some proof ← solveSepEq args[1]! args[2]! then
        goal.assign proof
        return true
    for localDecl? in (← getLCtx).decls.toArray.reverse do
      if let some localDecl := localDecl? then
        if let some proof ← solveFromHypothesis target localDecl then
          goal.assign proof
          return true
    return false

syntax (name := ecancel) "ecancel" : tactic

@[tactic ecancel]
def evalEcancel : Tactic :=
  fun _stx : Syntax => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let solved ← ecancelGoal goal
  unless solved do
    throwError "ecancel: could not automatically solve goal {target}"
  replaceMainGoal []

end Kraken.Tactic
end
