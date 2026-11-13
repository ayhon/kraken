module

public import Kraken.OmniSemantics
public import Kraken.Tactics.Separation
public import Kraken.Tactics.Residue

/-!
# Single-Step Symbolic Execution (`kstep`)

`Sym`-based symbolic execution tactic (`kstep` / `symKStep`) that steps through `Directives.interp`
and `Effects.All`, normalises `let`-bound instruction residues, applies `@[kspec]` memory and
instruction specification lemmas (with automatic separation-logic and byte-slice matching), and
resolves branch conditions (`ite`) using context hypotheses, `@[kcond]` flag projections, `omega`,
and `grind`.
-/

public meta section

open Lean Meta Elab Tactic Kraken Kraken.Tactic
open Sym Sym.DSimp

/-! ### Step Rewriting Lemmas -/

run_meta do
  let info ← getConstInfo ``Directives.interp
  let val := mkConst ``Directives.interp (info.levelParams.map mkLevelParam)
  addAndCompile (.defnDecl {
    name := `Directives.interpHold
    levelParams := info.levelParams
    type := info.type
    value := val
    hints := .regular 0
    safety := .safe
    all := [`Directives.interpHold]
  })

theorem Effects_All_interp_to_hold {D MD : Type} [ArchDirective D MD] [Labels]
    (post : TracedPost MD) (ds : List (Kraken.Sized D)) (s : MD) (pc : Int64)
    (ret : Int64 → MD → Kraken.Effects MD) :
    Kraken.Effects.All post (Directives.interp ds s pc ret) =
    Kraken.Effects.All post (Directives.interpHold ds s pc ret) := by rfl

theorem Effects_All_hold_to_interp {D MD : Type} [ArchDirective D MD] [Labels]
    (post : TracedPost MD) (ds : List (Kraken.Sized D)) (s : MD) (pc : Int64)
    (ret : Int64 → MD → Kraken.Effects MD) :
    Kraken.Effects.All post (Directives.interpHold ds s pc ret) =
    Kraken.Effects.All post (Directives.interp ds s pc ret) := by rfl

theorem Effects_All_interp_nil {D MD : Type} [ArchDirective D MD] [Labels]
    (post : TracedPost MD) (s : MD) (pc : Int64) (ret : Int64 → MD → Kraken.Effects MD) :
    Kraken.Effects.All post (Directives.interpHold ([] : List (Kraken.Sized D)) s pc ret) =
    Kraken.Effects.All post (ret pc s) := by rfl

theorem Effects_All_ite_true {MD : Type} (post : TracedPost MD)
    {c : Prop} [inst : Decidable c] (hc : c) (t f : Kraken.Effects MD) :
    Kraken.Effects.All post (@ite _ c inst t f) =
    Kraken.Effects.All post t := by
  simp [hc]

theorem Effects_All_ite_false {MD : Type} (post : TracedPost MD)
    {c : Prop} [inst : Decidable c] (hnc : ¬ c) (t f : Kraken.Effects MD) :
    Kraken.Effects.All post (@ite _ c inst t f) =
    Kraken.Effects.All post f := by
  simp [hnc]

theorem Effects_All_interp_cons {D MD : Type} [ArchDirective D MD] [Labels]
    (post : TracedPost MD) (d : D) (sz : Nat) (ds : List (Kraken.Sized D)) (s : MD) (pc : Int64)
    (ret : Int64 → MD → Kraken.Effects MD) :
    Kraken.Effects.All post (Directives.interpHold ({directive := d, size := sz} :: ds) s pc ret) =
    Kraken.Effects.All
      (onNextPost post (fun s => Directives.interpHold ds s (pc + .ofNat sz) ret) ret)
      (ArchDirective.interp d s (.mk pc (pc + .ofNat sz))) :=
  Effects.All_onNext _ _ _ _

theorem Effects_All_interp_cons' {D MD : Type} [ArchDirective D MD] [Labels]
    (post : TracedPost MD) (d : Kraken.Sized D) (ds : List (Kraken.Sized D)) (s : MD) (pc : Int64)
    (ret : Int64 → MD → Kraken.Effects MD) :
    Kraken.Effects.All post (Directives.interpHold (d :: ds) s pc ret) =
    Kraken.Effects.All
      (onNextPost post (fun s => Directives.interpHold ds s (pc + .ofNat d.size) ret) ret)
      (ArchDirective.interp d.directive s (.mk pc (pc + .ofNat d.size))) := by
  cases d
  exact Effects.All_onNext _ _ _ _

theorem Effects_All_done {MD : Type}
    (post : TracedPost MD) (a : Kraken.MachineState MD) :
    Kraken.Effects.All post (.done a) =
    post (.done a) [] := rfl

theorem Effects_All_next {MD : Type}
    (post : TracedPost MD) (s : MD) :
    Kraken.Effects.All post (.next s) =
    post (.next s) [] := rfl

theorem onNextPost_next {MD : Type}
    (post : TracedPost MD) (next : MD → Kraken.Effects MD) (jmp : Int64 → MD → Kraken.Effects MD)
    (s : MD) (tr : List LeakageEvent) :
    onNextPost post next jmp (.next s) tr =
    Kraken.Effects.All (post.prepend tr) (next s) := rfl

theorem onNextPost_done {MD : Type}
    (post : TracedPost MD) (next : MD → Kraken.Effects MD) (jmp : Int64 → MD → Kraken.Effects MD)
    (st : Kraken.MachineState MD) (tr : List LeakageEvent) :
    onNextPost post next jmp (.done st) tr =
    Kraken.Effects.All (post.prepend tr) (jmp st.pc st.data) := rfl

theorem Effects_All_onNextPost_next {MD : Type}
    (post : TracedPost MD) (next : MD → Kraken.Effects MD) (jmp : Int64 → MD → Kraken.Effects MD)
    (s : MD) :
    Kraken.Effects.All (onNextPost post next jmp) (.next s) =
    Kraken.Effects.All post (next s) := rfl

theorem Effects_All_onNextPost_interp_cons {D MD : Type} [ArchDirective D MD] [Labels]
    (post : TracedPost MD) (d : D) (sz : Nat) (ds : List (Kraken.Sized D))
    (pc : Int64) (ret : Int64 → MD → Kraken.Effects MD) (s : MD) :
    Kraken.Effects.All
      (onNextPost post (fun s => Directives.interpHold ({directive := d, size := sz} :: ds) s pc ret) ret)
      (.next s) =
    Kraken.Effects.All
      (onNextPost post (fun s => Directives.interpHold ds s (pc + .ofNat sz) ret) ret)
      (ArchDirective.interp d s (.mk pc (pc + .ofNat sz))) :=
  Effects.All_onNext _ _ _ _

theorem Effects_All_onNextPost_interp_nil {D MD : Type} [ArchDirective D MD] [Labels]
    (post : TracedPost MD) (pc : Int64) (ret : Int64 → MD → Kraken.Effects MD) (s : MD) :
    Kraken.Effects.All
      (onNextPost post (fun s => Directives.interpHold ([] : List (Kraken.Sized D)) s pc ret) ret)
      (.next s) =
    Kraken.Effects.All post (ret pc s) := by rfl

theorem Effects_All_onNextPost_done {MD : Type}
    (post : TracedPost MD) (next : MD → Kraken.Effects MD) (jmp : Int64 → MD → Kraken.Effects MD)
    (st : Kraken.MachineState MD) :
    Kraken.Effects.All (onNextPost post next jmp) (.done st) =
    Kraken.Effects.All post (jmp st.pc st.data) := rfl

theorem Effects_All_undefined {MD α : Type} [NondetSupportingType α]
    (post : TracedPost MD) (cont : α → Kraken.Effects MD) :
    Kraken.Effects.All post (@Kraken.Effects.undefined MD α _ cont) =
    (∀ v : α, (cont v).All post) := rfl

theorem Effects_All_require_read_access {MD : Type}
    (post : TracedPost MD) (span : Std.Rco AddressBound) (cont : Unit → Kraken.Effects MD) :
    Kraken.Effects.All post (.require_read_access span cont) =
    (cont ()).All (post.consEvent (.read span)) := rfl

theorem Effects_All_require_write_access {MD : Type}
    (post : TracedPost MD) (span : Std.Rco AddressBound) (cont : Unit → Kraken.Effects MD) :
    Kraken.Effects.All post (.require_write_access span cont) =
    (cont ()).All (post.consEvent (.write span)) := rfl

theorem Effects_All_require_exec_access {MD : Type}
    (post : TracedPost MD) (p : Std.Rco Int64) (cont : Unit → Kraken.Effects MD) :
    Kraken.Effects.All post (.require_exec_access p cont) =
    (cont ()).All (post.consEvent (.exec p)) := rfl

theorem Effects_All_require_const_time {MD : Type}
    (post : TracedPost MD) (vals : List (BitVec 64)) (cont : Unit → Kraken.Effects MD) :
    Kraken.Effects.All post (.require_const_time vals cont) =
    (cont ()).All (post.consEvent (.var_time vals)) := rfl

theorem Effects_All_onNextPost_require_read_access {MD : Type}
    (post : TracedPost MD) (next : MD → Kraken.Effects MD) (jmp : Int64 → MD → Kraken.Effects MD)
    (span : Std.Rco AddressBound) (cont : Unit → Kraken.Effects MD) :
    Kraken.Effects.All (onNextPost post next jmp) (.require_read_access span cont) =
    (cont ()).All (onNextPost (post.consEvent (.read span)) next jmp) := rfl

theorem Effects_All_onNextPost_require_write_access {MD : Type}
    (post : TracedPost MD) (next : MD → Kraken.Effects MD) (jmp : Int64 → MD → Kraken.Effects MD)
    (span : Std.Rco AddressBound) (cont : Unit → Kraken.Effects MD) :
    Kraken.Effects.All (onNextPost post next jmp) (.require_write_access span cont) =
    (cont ()).All (onNextPost (post.consEvent (.write span)) next jmp) := rfl

theorem Effects_All_onNextPost_require_exec_access {MD : Type}
    (post : TracedPost MD) (next : MD → Kraken.Effects MD) (jmp : Int64 → MD → Kraken.Effects MD)
    (p : Std.Rco Int64) (cont : Unit → Kraken.Effects MD) :
    Kraken.Effects.All (onNextPost post next jmp) (.require_exec_access p cont) =
    (cont ()).All (onNextPost (post.consEvent (.exec p)) next jmp) := rfl

theorem Effects_All_onNextPost_require_const_time {MD : Type}
    (post : TracedPost MD) (next : MD → Kraken.Effects MD) (jmp : Int64 → MD → Kraken.Effects MD)
    (vals : List (BitVec 64)) (cont : Unit → Kraken.Effects MD) :
    Kraken.Effects.All (onNextPost post next jmp) (.require_const_time vals cont) =
    (cont ()).All (onNextPost (post.consEvent (.var_time vals)) next jmp) := rfl

theorem Effects_All_onNextPost_prepend {MD : Type}
    (post : TracedPost MD) (next : MD → Kraken.Effects MD) (jmp : Int64 → MD → Kraken.Effects MD)
    (pfx : List LeakageEvent) (eff : Kraken.Effects MD) :
    Kraken.Effects.All ((onNextPost post next jmp).prepend pfx) eff =
    Kraken.Effects.All (onNextPost (post.prepend pfx) next jmp) eff := by
  have h : (onNextPost post next jmp).prepend pfx = onNextPost (post.prepend pfx) next jmp := by
    funext r tr
    simp only [TracedPost.prepend, onNextPost, TracedPost.prepend_append]
  rw [h]

/-! ### Options, Configuration, and Syntax -/

initialize registerTraceClass `Kraken.kstep
initialize registerTraceClass `Kraken.kstep.phase

register_option kraken.kstep.normalizeLets : Bool := {
  defValue := true
  descr := "kstep: bring the values of `let`-bound intermediate results into the normal form before introducing them"
}

structure KStepConfig where
  debug := false
declare_term_config_elab elabKStepConfig KStepConfig

syntax (name := tacticKStep) "kstep" optConfig (ppSpace num)? : tactic
syntax (name := symKStep) "kstep" optConfig (ppSpace num)? : grind

/-- Check whether `e` (under leading `let` bindings and metadata) is an `Effects.All` goal. -/
def isEffectsAll (e : Expr) : Bool :=
  match e with
  | .letE _ _ _ body _ => isEffectsAll body
  | .mdata _ e => isEffectsAll e
  | _ => e.isAppOfArity ``Kraken.Effects.All 3

/-! ### `Sym.DSimp` and `Sym.Simp` Procedures -/

partial def peelLambdaLets (f : Expr) (args : Array Expr) (fvars : Array Expr)
    (k : Expr → Array Expr → DSimpM Result) : DSimpM Result := do
  match f with
  | .lam binderName binderType body binderInfo =>
    match body with
    | .letE letName letType letVal letBody _ =>
      if !letType.hasLooseBVar 0 && !letVal.hasLooseBVar 0 then
        withLetDecl letName letType letVal fun fvarLet => do
          let instBody : Expr := letBody.instantiate1 fvarLet
          let newLambda := .lam binderName binderType instBody binderInfo
          peelLambdaLets newLambda args (fvars.push fvarLet) k
      else
        k (mkAppN f args) fvars
    | _ => k (mkAppN f args) fvars
  | _ => k (mkAppN f args) fvars

partial def peelLets (e : Expr) (fvars : Array Expr)
    (k : Expr → Array Expr → DSimpM Result) : DSimpM Result := do
  if e.hasLooseBVars then
    return ← k e fvars
  match e with
  | .letE name type val body _ =>
    withLetDecl name type val fun fvar =>
      peelLets (body.instantiate1 fvar) (fvars.push fvar) k
  | _ =>
    if e.isApp && e.getAppFn.isLambda then
      peelLambdaLets e.getAppFn e.getAppArgs fvars k
    else
      k e fvars

partial def peelArgsLets (args : Array Expr) (i : Nat) (peeled : Array Expr) (fvars : Array Expr)
    (k : Array Expr → Array Expr → DSimpM Result) : DSimpM Result := do
  if h : i < args.size then
    let arg := args[i]
    peelLets arg fvars fun arg' fvars' =>
      peelArgsLets args (i + 1) (peeled.push arg') fvars' k
  else
    k peeled fvars

/-- Hoist `let`-bindings from argument positions and unfold declarations in `targets`. -/
def kdeltaBetaOnly (targets : List Name) : DSimproc := fun e => do
  unless e.isApp && targets.any e.getAppFn'.isConstOf do return .rfl
  let f := e.getAppFn'
  let args := e.getAppArgs
  peelArgsLets args 0 #[] #[] fun (args : Array Expr) (fvars : Array Expr) => do
    let e_rebuilt := mkAppN f args
    if f.isConstOf ``Kraken.Effects.All then
      if fvars.size > 0 then
        let e' ← shareCommon e_rebuilt
        let e'' ← mkLetFVars fvars e'
        return .step e''
      else
        return .rfl
    else
      if let some e' ← Meta.unfoldDefinition? e_rebuilt true then
        let e' ← shareCommon e'
        let e'' ← betaRevS e'.getAppFn e'.getAppRevArgs
        let e'' ← mkLetFVars fvars e''
        return .step e''
      else if fvars.size > 0 then
        let e' ← shareCommon e_rebuilt
        let e'' ← mkLetFVars fvars e'
        return .step e''
      else
        return .rfl

def klog : DSimproc := fun e => do
  let s := (← get).numSteps
  if e.isAppOfArity ``Kraken.Effects.All 3 then
    trace[Kraken.kstep] "step {s} visiting\n{e}"
  return .rfl

def kdsimpMatch : DSimproc := fun e => do
  if e.hasLooseBVars then return .rfl
  if e.isAppOfArity ``ite 5 then
    let α := e.getArg! 0
    let c := e.getArg! 1
    if !c.hasFVar && !c.hasLooseBVars then
      let inst ← withDefault (whnf (e.getArg! 2))
      if inst.isAppOfArity ``Decidable.isTrue 2 then
        return .step (← share (e.getArg! 3))
      if inst.isAppOfArity ``Decidable.isFalse 2 then
        return .step (← share (e.getArg! 4))
    if α.isAppOf ``Kraken.Effects then
      let c' ← match (← Sym.DSimp.dsimp c) with
        | .rfl _ => pure c
        | .step c' _ => pure c'
      return ← peelLets c' #[] fun c'' fvars => do
        if fvars.isEmpty && isSameExpr c c'' then
          return .rfl (done := true)
        else
          let args := e.getAppArgs.set! 1 c''
          let e' ← shareCommon (mkAppN e.getAppFn args)
          let e'' ← mkLetFVars fvars e'
          return .step e'' (done := true)
  let some e' ← reduceRecMatcher? e | return .rfl
  let e'' ← Sym.foldProjs e'
  if isSameExpr e e'' then
    return .rfl
  else
    return .step (← share e'')

def kbeta : DSimproc := fun e => do
  unless e.isApp do return .rfl
  let f := e.getAppFn
  if f.isHeadBetaTargetFn false then
    let e' ← betaRevS f e.getAppRevArgs
    return .step e'
  else
    return .rfl

def kdsimpProj : DSimproc := fun e => do
  if e.hasLooseBVars then return .rfl
  let f := e.getAppFn
  let .const declName _ := f | return .rfl
  let some projInfo ← getProjectionFnInfo? declName | return .rfl
  let reduceProjCont? (e? : Option Expr) : DSimpM Result := do
    match e? with
    | none   => return .rfl
    | some e =>
      match (← reduceProj? e.getAppFn) with
      | some f => return .step (← share (mkAppN f e.getAppArgs))
      | none   => return .rfl
  if projInfo.fromClass then
    unless e.getAppNumArgs > projInfo.numParams do
      return .rfl
    let major := e.getArg! projInfo.numParams
    unless (← isConstructorApp major) do
      return .rfl
    if backward.whnf.reducibleClassField.get (← getOptions) then
      let some e' ← unfoldDefinition? e (ignoreTransparency := true) | return .rfl
      return .step (← share e')
    else
      reduceProjCont? (← unfoldDefinition? e (ignoreTransparency := true))
  else
    reduceProjCont? (← unfoldDefinition? e)

def kLiftLets : DSimproc := fun e => do
  unless e.isApp && e.getAppFn'.isConstOf ``Kraken.Effects.All do return .rfl
  let (es, st) ← ExtractLets.extract #[e] |>.run {} |>.run' {} |>.run { givenNames := [] }
  unless st.decls.size > 0 do return .rfl
  let e' := Meta.ExtractLets.mkLetDecls st.decls es[0]!
  let e' ← Sym.share e'
  return .step e'

private def isBitwiseOp (e : Expr) : Bool :=
  e.isAppOf ``HXor.hXor || e.isAppOf ``XorOp.xor || e.isAppOf ``BitVec.xor || e.isAppOf ``Nat.xor ||
  e.isAppOf ``HAnd.hAnd || e.isAppOf ``AndOp.and || e.isAppOf ``BitVec.and || e.isAppOf ``Nat.land ||
  e.isAppOf ``HOr.hOr || e.isAppOf ``OrOp.or || e.isAppOf ``BitVec.or || e.isAppOf ``Nat.lor

private def kEvalGroundNoBitwise : DSimproc := fun e => do
  if isBitwiseOp e then return .rfl
  (evalGround : DSimproc) e

private def skipPostAndDepForallD : DSimproc := fun e => do
  if (e.isForall && !e.isArrow) || e.isAppOf ``Exists || e.isAppOf ``Or ||
     e.isAppOf ``TracedEventually || e.isAppOf ``TracedGoal ||
     e.isAppOf ``Kraken.Executable.mk then
    return .rfl (done := true)
  if e.isAppOfArity ``Eventually 4 then
    let args := e.getAppArgs
    let post := args[2]!
    let st := args[3]!
    let post' ← match (← Sym.DSimp.dsimp post) with
      | .rfl _ => pure post
      | .step post' _ => pure post'
    let st' ← match (← Sym.DSimp.dsimp st) with
      | .rfl _ => pure st
      | .step st' _ => pure st'
    return ← peelLets st' #[] fun st'' fvars => do
      if fvars.isEmpty && isSameExpr post post' && isSameExpr st st'' then
        return .rfl (done := true)
      else
        let args' := (args.set! 2 post').set! 3 st''
        let e' ← shareCommon (mkAppN e.getAppFn args')
        let e'' ← mkLetFVars fvars e'
        return .step e'' (done := true)
  if e.isAppOfArity ``Kraken.Effects.All 3 then
    let eff := e.appArg!
    let eff' ← match (← Sym.DSimp.dsimp eff) with
      | .rfl _ => pure eff
      | .step eff' _ => pure eff'
    return ← peelLets eff' #[] fun eff'' fvars => do
      if fvars.isEmpty && isSameExpr eff eff'' then
        return .rfl (done := true)
      else
        let e' ← shareCommon (mkApp e.appFn! eff'')
        let e'' ← mkLetFVars fvars e'
        return .step e'' (done := true)
  if e.isAppOf ``Kraken.Effects.require_exec_access ||
     e.isAppOf ``Kraken.Effects.require_const_time ||
     e.isAppOf ``Kraken.Effects.require_read_access ||
     e.isAppOf ``Kraken.Effects.require_write_access ||
     e.isAppOf ``Kraken.Effects.undefined then
    return .rfl (done := true)
  if e.isAppOf ``Directives.interp || e.isAppOf `Directives.interpHold then
    if e.getAppNumArgs == 8 then
      let args := e.getAppArgs
      let ds := args[4]!
      let s := args[5]!
      let pc := args[6]!
      let ds' ←
        if ds.isAppOfArity ``List.cons 3 || ds.isAppOfArity ``List.nil 1 then
          pure ds
        else
          match (← Sym.DSimp.dsimp ds) with
          | .rfl _ => pure ds
          | .step ds' _ => pure ds'
      let s' ← match (← Sym.DSimp.dsimp s) with
        | .rfl _ => pure s
        | .step s' _ => pure s'
      let pc' ← match (← Sym.DSimp.dsimp pc) with
        | .rfl _ => pure pc
        | .step pc' _ => pure pc'
      return ← peelLets s' #[] fun s'' fvars1 =>
        peelLets pc' fvars1 fun pc'' fvars2 => do
          if fvars2.isEmpty && isSameExpr ds ds' && isSameExpr s s'' && isSameExpr pc pc'' then
            return .rfl (done := true)
          else
            let args' := ((args.set! 4 ds').set! 5 s'').set! 6 pc''
            let e' ← shareCommon (mkAppN e.getAppFn args')
            let e'' ← mkLetFVars fvars2 e'
            return .step e'' (done := true)
    else
      return .rfl (done := true)
  return .rfl

private def skipPostAndDepForall : Sym.Simp.Simproc := fun e => do
  if (e.isForall && !e.isArrow) || e.isAppOf ``Exists || e.isAppOf ``Or ||
     e.isAppOf ``TracedEventually || e.isAppOf ``Std.ExtHashMap.sep ||
     e.isAppOf ``Kraken.Executable.mk then
    return .rfl (done := true)
  if e.isAppOfArity ``Directives.interp 8 || e.isAppOfArity `Directives.interpHold 8 then
    match ← Sym.Simp.simpAppArgRange e 5 7 with
    | .step e' h _ cd => return .step e' h (done := true) (contextDependent := cd)
    | .rfl _ cd => return .rfl (done := true) (contextDependent := cd)
  if e.isAppOfArity ``Eventually 4 || e.isAppOfArity ``TracedGoal 4 then
    match ← Sym.Simp.simpAppArgRange e 3 4 with
    | .step e' h _ cd => return .step e' h (done := true) (contextDependent := cd)
    | .rfl _ cd => return .rfl (done := true) (contextDependent := cd)
  if e.isAppOfArity ``Kraken.Effects.All 3 then
    match ← Sym.Simp.simpAppArgRange e 2 3 with
    | .step e' h _ cd => return .step e' h (done := true) (contextDependent := cd)
    | .rfl _ cd => return .rfl (done := true) (contextDependent := cd)
  if e.isAppOfArity ``ite 5 && (e.getArg! 0).isAppOf ``Kraken.Effects then
    return ← Sym.Simp.simpControl e
  return .rfl

/-! ### Signed `BitVec 64` Offset Arithmetic for Memory Accesses -/

private partial def expandLets (e : Expr) : MetaM Expr := do
  let e ← if e.hasExprMVar then instantiateMVars e else pure e
  match e with
  | .fvar fvarId =>
    if let some localDecl ← fvarId.findDecl? then
      if let some val := localDecl.value? then
        return ← expandLets val
    return e
  | .letE _ _ v b _ =>
    let v' ← expandLets v
    expandLets (b.instantiate1 v')
  | .app f a =>
    return e.updateApp! (← expandLets f) (← expandLets a)
  | .mdata _ b =>
    expandLets b
  | .proj _ _ s =>
    return e.updateProj! (← expandLets s)
  | _ => return e

private partial def getBitVec64Value? (e : Expr) : MetaM (Option (BitVec 64)) := do
  let e := e.consumeMData
  if let some ⟨w, bv⟩ ← getBitVecValue? e then
    if h : w = 64 then
      return some (h ▸ bv)
    else
      return none
  else if e.isAppOfArity ``Neg.neg 3 || e.isAppOfArity ``BitVec.neg 2 then
    let a := e.appArg!
    return (- ·) <$> (← getBitVec64Value? a)
  else if e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``BitVec.add 3 then
    let args := e.getAppArgs
    let a := args[args.size - 2]!
    let b := args[args.size - 1]!
    match ← getBitVec64Value? a, ← getBitVec64Value? b with
    | some va, some vb => return some (va + vb)
    | _, _ => return none
  else if e.isAppOfArity ``HSub.hSub 6 || e.isAppOfArity ``BitVec.sub 3 then
    let args := e.getAppArgs
    let a := args[args.size - 2]!
    let b := args[args.size - 1]!
    match ← getBitVec64Value? a, ← getBitVec64Value? b with
    | some va, some vb => return some (va - vb)
    | _, _ => return none
  else
    return none

private partial def peelBitVecAddSignedOffset (e : Expr) : MetaM (Expr × Int) := do
  let e ← match e.consumeMData with
    | .fvar fvarId =>
      match ← fvarId.getValue? with
      | some val => pure val.consumeMData
      | none => pure e.consumeMData
    | e' => pure e'
  if e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``BitVec.add 3 then
    let args := e.getAppArgs
    let a := args[args.size - 2]!
    let b := args[args.size - 1]!
    if let some bv ← getBitVec64Value? b then
      let n := bv.toInt
      if n != 0 && -4096 ≤ n && n ≤ 4096 then
        let (base, off) ← peelBitVecAddSignedOffset a
        return (base, off + n)
  else if e.isAppOfArity ``HSub.hSub 6 || e.isAppOfArity ``BitVec.sub 3 then
    let args := e.getAppArgs
    let a := args[args.size - 2]!
    let b := args[args.size - 1]!
    if let some bv ← getBitVec64Value? b then
      let n := bv.toInt
      if n != 0 && -4096 ≤ n && n ≤ 4096 then
        let (base, off) ← peelBitVecAddSignedOffset a
        return (base, off - n)
  return (e, 0)

private def peelSingleBitVecAddSignedOffset (e : Expr) : MetaM (Expr × Int × Option Expr) := do
  let e ← match e.consumeMData with
    | .fvar fvarId =>
      match ← fvarId.getValue? with
      | some val => pure val.consumeMData
      | none => pure e.consumeMData
    | e' => pure e'
  if e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``BitVec.add 3 then
    let args := e.getAppArgs
    let a := args[args.size - 2]!
    let b := args[args.size - 1]!.consumeMData
    if let some bv ← getBitVec64Value? b then
      let n := bv.toInt
      if n != 0 && -4096 ≤ n && n ≤ 4096 then
        return (a, n, some b)
  return (e, 0, none)

/-- Fast proof of `lhs = rhs` for `BitVec 64` sums of the form `(base + a) + b = base + c`. -/
private def tryProveBitVecAddEq (lhs rhs : Expr) : MetaM (Option Expr) := do
  if lhs == rhs then
    return some (← mkEqRefl lhs)
  let (lhsBase, lhsOff) ← peelBitVecAddSignedOffset lhs
  let (rhsBase, rhsOff) ← peelBitVecAddSignedOffset rhs
  if lhsOff != rhsOff then
    return none
  unless ← withReducible (isDefEq lhsBase rhsBase) do
    return none
  let (lhs1, lOff1, lArg1?) ← peelSingleBitVecAddSignedOffset lhs
  let (rhs1, rOff1, rArg1?) ← peelSingleBitVecAddSignedOffset rhs
  match lArg1?, rArg1? with
  | none, none =>
    return some (← mkExpectedTypeHint (← mkEqRefl lhs) (← mkEq lhs rhs))
  | some b, some c =>
    if lOff1 == rOff1 && (← withReducible (isDefEq lhs1 rhs1)) then
      return some (← mkExpectedTypeHint (← mkEqRefl lhs) (← mkEq lhs rhs))
    else
      let (lhs2, lOff2, lArg2?) ← peelSingleBitVecAddSignedOffset lhs1
      if let some a := lArg2? then
        if lOff1 + lOff2 == rOff1 && (← withReducible (isDefEq lhs2 rhs1)) then
          let hAdd ← mkExpectedTypeHint (← mkEqRefl c) (← mkEq (← mkAppM ``HAdd.hAdd #[a, b]) c)
          let prf := mkAppN (mkConst ``BitVec.add_add_eq_of_add_eq) #[mkNatLit 64, lhs2, a, b, c, hAdd]
          return some (← mkExpectedTypeHint prf (← mkEq lhs rhs))
      let (rhs2, rOff2, rArg2?) ← peelSingleBitVecAddSignedOffset rhs1
      if let some a := rArg2? then
        if rOff1 + rOff2 == lOff1 && (← withReducible (isDefEq lhs1 rhs2)) then
          let bR := c
          let cL := b
          let hAdd ← mkExpectedTypeHint (← mkEqRefl cL) (← mkEq (← mkAppM ``HAdd.hAdd #[a, bR]) cL)
          let prf := mkAppN (mkConst ``BitVec.add_eq_add_add_of_add_eq) #[mkNatLit 64, lhs1, a, bR, cL, hAdd]
          return some (← mkExpectedTypeHint prf (← mkEq lhs rhs))
      return none
  | _, _ =>
    return none

private def hasAddOrSub (e : Expr) : Bool :=
  match e with
  | .app f a =>
    f.isAppOf ``HAdd.hAdd || f.isAppOf ``BitVec.add ||
    f.isAppOf ``HSub.hSub || f.isAppOf ``BitVec.sub ||
    hasAddOrSub f || hasAddOrSub a
  | .mdata _ b => hasAddOrSub b
  | .proj _ _ s => hasAddOrSub s
  | _ => false

private def canSliceCandidate (cand : SepAtCandidate) (off : Nat) : Bool :=
  if cand.bs.isAppOfArity ``Int.toBytes 2 || cand.bs.isAppOfArity ``Nat.toBytes 2 then
    match (cand.bs.getArg! 0).nat? with
    | some k => off < k
    | none => true
  else if cand.bs.isAppOfArity ``List.take 3 then
    match (cand.bs.getArg! 1).nat? with
    | some k => off < k
    | none => true
  else if cand.bs.isAppOfArity ``UInt64.toBytes 1 then
    off < 8
  else
    true

/-! ### Target Rewriting and `let` Normalization -/

private def preprocessGoalIfNeeded (goal : Grind.Goal) : Grind.GrindTacticM Grind.Goal := do
  let target ← goal.mvarId.getType
  unless target.hasExprMVar do return goal
  let targetInst ← instantiateMVars target
  if isSameExpr target targetInst then return goal
  let target' ← Grind.liftSymM (Sym.preprocessExpr targetInst)
  let mvarId ← goal.mvarId.replaceTargetDefEq target'
  return { goal with mvarId }

/-- Bring the value of a leading `let` into the `ksimp` normal form before it is introduced into
the context. -/
private def simpLetValue (goal : Grind.Goal) : Grind.GrindTacticM Grind.Goal := goal.withContext do
  let t := (← instantiateMVars (← goal.mvarId.getType)).consumeMData
  let .letE n ty v b nd := t | return goal
  unless kraken.kstep.normalizeLets.get (← getOptions) do return goal
  if v.hasLooseBVars then return goal
  unless ← isWordType ty do return goal
  let v₀ ← inlineAtomicLets v
  let v₁ ← reduceStuckMatchers v₀
  let (v', h?) ← match ← simpNormalForm v₁ with
    | none => pure (v₁, none)
    | some (v', h) => pure (v', some h)
  if v' == v then return goal
  trace[Kraken.kstep.phase] "simpLetValue {n} := {v} ↦ {v'}"
  let h ← match h? with
    | some h => pure h
    | none => mkExpectedTypeHint (← mkEqRefl v) (← mkEq v v')
  let f := mkLambda n .default ty b
  let eqPrf ← mkCongrArg f h
  let newTarget ← Grind.liftSymM (Sym.preprocessExpr (mkLet n ty v' b nd))
  let mvarId ← goal.mvarId.replaceTargetEq newTarget eqPrf
  return { goal with mvarId }

def rwTarget (goal : Grind.Goal) (symm : Bool) (term : Expr) :
    Grind.GrindTacticM (Grind.Goal × List Grind.Goal) := do
  goal.withContext do
    let target := (← instantiateMVars (← goal.mvarId.getType)).consumeMData
    let rootRewrite? : Option (Expr × Expr × List MVarId) ←
      if target.isAppOfArity ``Kraken.Effects.All 3 then
        let saved ← saveState
        try
          Term.withSynthesize do
            let heqType ← Sym.unfoldReducible (← instantiateMVars (← inferType term))
            let (xs, bis, eqType) ← forallMetaTelescopeReducing heqType
            let some (_, lhs, rhs) := eqType.eq? | failure
            let (lhs, rhs) := if symm then (rhs, lhs) else (lhs, rhs)
            let mut proof := mkAppN term xs
            if symm then
              proof ← mkEqSymm proof
            let eNewInner ←
              if lhs.isAppOfArity ``Kraken.Effects.All 3 then
                if ← isDefEq lhs target then
                  pure rhs
                else
                  failure
              else
                if ← isDefEq lhs target.appArg! then
                  proof ← mkCongrArg target.appFn! proof
                  pure (mkApp target.appFn! rhs)
                else
                  failure
            for x in xs, bi in bis do
              if bi.isInstImplicit && !(← x.mvarId!.isAssigned) then
                x.mvarId!.assign (← synthInstance (← inferType x))
            let eqProof ← instantiateMVars proof
            let eNew ← instantiateMVars eNewInner
            let mvarIds := (xs.map (·.mvarId!)).toList
            pure (some (eNew, eqProof, mvarIds))
        catch _ =>
          restoreState saved
          pure none
      else
        pure none
    let (eNewRaw, eqProof, mvarIds) ← match rootRewrite? with
      | some res => pure res
      | none =>
        let mvarCounterSaved := (← getMCtx).mvarCounter
        let r ← Term.withSynthesize do
          let heq := term
          let heqType ← instantiateMVars (← inferType heq)
          let heqType' ← Sym.unfoldReducible heqType
          let heq ← if isSameExpr heqType heqType' then pure heq else mkExpectedTypeHint heq heqType'
          goal.mvarId.rewrite target heq symm
        let mctx ← getMCtx
        let mvarIds := r.mvarIds.filter fun mvarId => (mctx.getDecl mvarId |>.index) >= mvarCounterSaved
        pure (r.eNew, r.eqProof, mvarIds)
    let eNew ← Grind.liftSymM <| Sym.preprocessExpr eNewRaw
    let mvarId ← goal.mvarId.replaceTargetEq eNew eqProof
    let mvarIds ← mvarIds.filterM fun mvarId => return !(← mvarId.isAssigned)
    let sideGoals ← mvarIds.mapM fun mvarId => do
      let target ← mvarId.getType
      let targetInst ← instantiateMVars target
      let target' ← Grind.liftSymM <| Sym.preprocessExpr targetInst
      if isSameExpr target target' then
        mvarId.setKind .syntheticOpaque
        return { goal with mvarId }
      else
        let mvarId ← mvarId.replaceTargetDefEq target'
        return { goal with mvarId }
    pure ({ goal with mvarId }, sideGoals)

/-! ### The `kstep` Symbolic Execution Loop -/

@[grind_tactic symKStep]
partial def evalSymKStep : Grind.GrindTactic :=
  fun stx : Syntax => do
  let cfg := stx[1]
  let _config ← elabKStepConfig cfg
  let maxSteps? : Option Nat := if stx[2].isNone then none else some stx[2][0].toNat
  let goal : Grind.Goal ← Grind.getMainGoal
  let goal := { goal with mvarId := ← Grind.liftSymM (Sym.preprocessMVar goal.mvarId) }
  let env ← getEnv

  let declsForDSimp := (kstepExtension.getState env).toList
  let maxInstrCount ← maxSteps?.mapM (IO.mkRef ·)
  let kdsimpDecls := kdeltaBetaOnly declsForDSimp
  let dsimpCore := skipPostAndDepForallD >> kEvalGroundNoBitwise >> kdsimpDecls >> kdsimpMatch >> kdsimpProj >> kbeta
  let dsimpPre := if ← isTracingEnabledFor `Kraken.kstep then klog >> dsimpCore else dsimpCore

  let simpTheorems ← ksimpExt.getTheorems
  let simpMethods : Sym.Simp.Methods := {
    pre := skipPostAndDepForall
    post := Sym.Simp.evalGround >> simpTheorems.rewrite
  }

  let specLemmas := (kspecExtension.getState env).toList
  let specTree : DiscrTree Name ← specLemmas.foldlM (fun specTree name => do
    let (pat, _) ← mkEqPatternFromDecl name
    pure (insertPattern specTree pat name)
  ) {}

  let introsIf (goal : Grind.Goal) : Grind.GrindTacticM Grind.Goal := do
    let inner := (← instantiateMVars (← goal.mvarId.getType)).consumeMData
    unless inner.isLet || inner.isForall do return goal
    let rec introLoop (goal : Grind.Goal) (fuel : Nat) : Grind.GrindTacticM Grind.Goal := do
      if fuel = 0 then return goal
      let goal ← simpLetValue goal
      match ← Grind.liftGrindM (goal.introN 1) with
      | Grind.IntrosResult.failed => pure goal
      | .goal _ goal => introLoop goal (fuel - 1)
    introLoop goal 1024

  let tStep ← IO.mkRef (0 : Nat)
  let tSimp ← IO.mkRef (0 : Nat)
  let tSpec ← IO.mkRef (0 : Nat)
  let tIte ← IO.mkRef (0 : Nat)
  let tPre ← IO.mkRef (0 : Nat)
  let timed {α} (r : IO.Ref Nat) (x : Grind.GrindTacticM α) : Grind.GrindTacticM α := do
    let t0 ← IO.monoNanosNow
    try x finally
      let t1 ← IO.monoNanosNow
      r.modify (· + (t1 - t0))

  let rec go (goal : Grind.Goal) : Grind.GrindTacticM (Grind.Goal × List Grind.Goal) := do
    let goal ← timed tPre <| goal.withContext (preprocessGoalIfNeeded goal)
    -- STEP 1: dsimp and step through Directives.interp via equational theorems
    let rec stepDirectivesLoop (goal : Grind.Goal) : Grind.GrindTacticM Grind.Goal := do
      let goal ← goal.withContext do
        let inner := (← instantiateMVars (← goal.mvarId.getType)).consumeMData
        if inner.isForall && !inner.isArrow then
          introsIf goal
        else
          return goal
      let goal ← goal.withContext do
        let target ← goal.mvarId.getType
        let target' ← Grind.liftGrindM <|
          Sym.dsimp
            (config := { maxSteps := 1000000 })
            (methods := { pre := dsimpPre })
            target
        let mvarId ←
          if isSameExpr target target' then
            pure goal.mvarId
          else
            goal.mvarId.replaceTargetDefEq target'
        let mvarId ←
          if (target'.find? isBitwiseOp).isSome then
            let target'' ← Grind.liftGrindM <|
              Sym.dsimp
                (config := { maxSteps := 1000000 })
                (methods := { pre := skipPostAndDepForallD >> evalGround })
                target'
            if isSameExpr target' target'' then
              pure mvarId
            else
              mvarId.replaceTargetDefEq target''
          else
            pure mvarId
        introsIf ({ goal with mvarId })
      let stepEq? ← goal.withContext do
        let inner := (← instantiateMVars (← goal.mvarId.getType)).consumeMData
        if inner.isAppOfArity ``onNextPost 6 then
          let iArgs := inner.getAppArgs
          let MD := iArgs[0]!
          let post := iArgs[1]!
          let next := iArgs[2]!
          let jmp := iArgs[3]!
          let r := iArgs[4]!
          let tr := iArgs[5]!
          if r.isAppOfArity ``StepResult.next 2 then
            let s := r.getArg! 1
            let eqPrf := mkAppN (mkConst ``onNextPost_next) #[MD, post, next, jmp, s, tr]
            let rhs ← Grind.liftSymM (Sym.preprocessExpr (← inferType eqPrf).appArg!)
            return some (false, true, rhs, eqPrf)
          else if r.isAppOfArity ``StepResult.done 2 then
            let st := r.getArg! 1
            let eqPrf := mkAppN (mkConst ``onNextPost_done) #[MD, post, next, jmp, st, tr]
            let rhs ← Grind.liftSymM (Sym.preprocessExpr (← inferType eqPrf).appArg!)
            return some (false, true, rhs, eqPrf)
        unless inner.isAppOfArity ``Kraken.Effects.All 3 do return none
        let MD := inner.getArg! 0
        let post := inner.getArg! 1
        let eff := inner.getArg! 2
        if post.isAppOfArity ``TracedPost.prepend 3 && (post.getArg! 2).isAppOfArity ``onNextPost 4 then
          let pfx := post.getArg! 1
          let oArgs := (post.getArg! 2).getAppArgs
          let eqPrf := mkAppN (mkConst ``Effects_All_onNextPost_prepend) #[MD, oArgs[1]!, oArgs[2]!, oArgs[3]!, pfx, eff]
          let rhs ← Grind.liftSymM (Sym.preprocessExpr (← inferType eqPrf).appArg!)
          return some (false, true, rhs, eqPrf)
        if eff.isAppOfArity ``Kraken.Effects.require_exec_access 3 then
          let p := eff.getArg! 1
          let cont := eff.getArg! 2
          let eqPrf :=
            if post.isAppOfArity ``onNextPost 4 then
              let oArgs := post.getAppArgs
              mkAppN (mkConst ``Effects_All_onNextPost_require_exec_access) #[MD, oArgs[1]!, oArgs[2]!, oArgs[3]!, p, cont]
            else
              mkAppN (mkConst ``Effects_All_require_exec_access) #[MD, post, p, cont]
          let rhs ← Grind.liftSymM (Sym.preprocessExpr (← inferType eqPrf).appArg!)
          return some (false, true, rhs, eqPrf)
        else if eff.isAppOfArity ``Kraken.Effects.require_const_time 3 then
          let vals := eff.getArg! 1
          let cont := eff.getArg! 2
          let eqPrf :=
            if post.isAppOfArity ``onNextPost 4 then
              let oArgs := post.getAppArgs
              mkAppN (mkConst ``Effects_All_onNextPost_require_const_time) #[MD, oArgs[1]!, oArgs[2]!, oArgs[3]!, vals, cont]
            else
              mkAppN (mkConst ``Effects_All_require_const_time) #[MD, post, vals, cont]
          let rhs ← Grind.liftSymM (Sym.preprocessExpr (← inferType eqPrf).appArg!)
          return some (false, true, rhs, eqPrf)
        else if eff.isAppOfArity ``Kraken.Effects.require_read_access 3 then
          let span := eff.getArg! 1
          let cont := eff.getArg! 2
          let eqPrf :=
            if post.isAppOfArity ``onNextPost 4 then
              let oArgs := post.getAppArgs
              mkAppN (mkConst ``Effects_All_onNextPost_require_read_access) #[MD, oArgs[1]!, oArgs[2]!, oArgs[3]!, span, cont]
            else
              mkAppN (mkConst ``Effects_All_require_read_access) #[MD, post, span, cont]
          let rhs ← Grind.liftSymM (Sym.preprocessExpr (← inferType eqPrf).appArg!)
          return some (false, true, rhs, eqPrf)
        else if eff.isAppOfArity ``Kraken.Effects.require_write_access 3 then
          let span := eff.getArg! 1
          let cont := eff.getArg! 2
          let eqPrf :=
            if post.isAppOfArity ``onNextPost 4 then
              let oArgs := post.getAppArgs
              mkAppN (mkConst ``Effects_All_onNextPost_require_write_access) #[MD, oArgs[1]!, oArgs[2]!, oArgs[3]!, span, cont]
            else
              mkAppN (mkConst ``Effects_All_require_write_access) #[MD, post, span, cont]
          let rhs ← Grind.liftSymM (Sym.preprocessExpr (← inferType eqPrf).appArg!)
          return some (false, true, rhs, eqPrf)
        else if eff.isAppOfArity ``Kraken.Effects.done 2 || eff.isAppOfArity ``Kraken.Effects.next 2 then
          let isDone := eff.isAppOfArity ``Kraken.Effects.done 2
          let arg := eff.getArg! 1
          let maxCount ← maxInstrCount.mapM (·.get)
          let (decCount, eqPrf) :=
            if post.isAppOfArity ``onNextPost 4 then
              let oArgs := post.getAppArgs
              let post₀ := oArgs[1]!
              let next := oArgs[2]!
              let jmp := oArgs[3]!
              if isDone then
                (false, mkAppN (mkConst ``Effects_All_onNextPost_done) #[MD, post₀, next, jmp, arg])
              else
                let interpNext? : Option (Bool × Expr) := match next with
                  | .lam _ _ body _ =>
                    if body.isAppOfArity `Directives.interpHold 8 && body.getArg! 5 == .bvar 0 then
                      let bArgs := body.getAppArgs
                      let D := bArgs[0]!
                      let inst := bArgs[2]!
                      let labels := bArgs[3]!
                      let ds := bArgs[4]!
                      let pc := bArgs[6]!
                      let ret := bArgs[7]!
                      if !ds.hasLooseBVars && !pc.hasLooseBVars && !ret.hasLooseBVars then
                        if ds.isAppOfArity ``List.nil 1 then
                          some (false, mkAppN (mkConst ``Effects_All_onNextPost_interp_nil)
                            #[D, MD, inst, labels, post₀, pc, ret, arg])
                        else if maxCount != .some 0 && ds.isAppOfArity ``List.cons 3 &&
                                (ds.getArg! 1).isAppOfArity ``Kraken.Sized.mk 3 then
                          let d := ds.getArg! 1
                          let dsTail := ds.getArg! 2
                          some (true, mkAppN (mkConst ``Effects_All_onNextPost_interp_cons)
                            #[D, MD, inst, labels, post₀, d.getArg! 1, d.getArg! 2, dsTail, pc, ret, arg])
                        else
                          none
                      else
                        none
                    else
                      none
                  | _ => none
                match interpNext? with
                | some res => res
                | none => (false, mkAppN (mkConst ``Effects_All_onNextPost_next) #[MD, post₀, next, jmp, arg])
            else
              (false, mkAppN (mkConst (if isDone then ``Effects_All_done else ``Effects_All_next)) #[MD, post, arg])
          let rhs ← Grind.liftSymM (Sym.preprocessExpr (← inferType eqPrf).appArg!)
          return some (decCount, true, rhs, eqPrf)
        else if eff.isAppOfArity ``Kraken.Effects.undefined 4 then
          let α := eff.getArg! 1
          let inst := eff.getArg! 2
          let cont := eff.getArg! 3
          let eqPrf := mkAppN (mkConst ``Effects_All_undefined) #[MD, α, inst, post, cont]
          let rhs ← Grind.liftSymM (Sym.preprocessExpr (← inferType eqPrf).appArg!)
          return some (false, true, rhs, eqPrf)
        else if eff.isAppOfArity ``Directives.interp 8 then
          if (← maxInstrCount.mapM (·.get)) = .some 0 then
            return none
          let iArgs := eff.getAppArgs
          let eqPrf := mkAppN (mkConst ``Effects_All_interp_to_hold)
            #[iArgs[0]!, iArgs[1]!, iArgs[2]!, iArgs[3]!, post, iArgs[4]!, iArgs[5]!, iArgs[6]!, iArgs[7]!]
          let rhs ← Grind.liftSymM (Sym.preprocessExpr (← inferType eqPrf).appArg!)
          return some (false, true, rhs, eqPrf)
        else if eff.isAppOfArity `Directives.interpHold 8 then
          let iArgs := eff.getAppArgs
          let D := iArgs[0]!
          let MD := iArgs[1]!
          let inst := iArgs[2]!
          let labels := iArgs[3]!
          let ds := iArgs[4]!
          let s := iArgs[5]!
          let pc := iArgs[6]!
          let ret := iArgs[7]!
          if ds.isAppOfArity ``List.nil 1 then
            let eqPrf := mkAppN (mkConst ``Effects_All_interp_nil)
              #[D, MD, inst, labels, post, s, pc, ret]
            let rhs ← Grind.liftSymM (Sym.preprocessExpr (← inferType eqPrf).appArg!)
            return some (false, true, rhs, eqPrf)
          else if (← maxInstrCount.mapM (·.get)) = .some 0 then
            let eqPrf := mkAppN (mkConst ``Effects_All_hold_to_interp)
              #[D, MD, inst, labels, post, ds, s, pc, ret]
            let rhs ← Grind.liftSymM (Sym.preprocessExpr (← inferType eqPrf).appArg!)
            return some (false, false, rhs, eqPrf)
          else if ds.isAppOfArity ``List.cons 3 then
            let d := ds.getArg! 1
            let dsTail := ds.getArg! 2
            let eqPrf :=
              if d.isAppOfArity ``Kraken.Sized.mk 3 then
                mkAppN (mkConst ``Effects_All_interp_cons)
                  #[D, MD, inst, labels, post, d.getArg! 1, d.getArg! 2, dsTail, s, pc, ret]
              else
                mkAppN (mkConst ``Effects_All_interp_cons')
                  #[D, MD, inst, labels, post, d, dsTail, s, pc, ret]
            let rhs ← Grind.liftSymM (Sym.preprocessExpr (← inferType eqPrf).appArg!)
            return some (true, true, rhs, eqPrf)
          else
            return none
        else
          return none
      match stepEq? with
      | some (decCount, keepLooping, rhs, eqPrf) =>
        if decCount then
          maxInstrCount.forM (fun r => r.modify (· - 1))
        let mvarId ← goal.withContext (goal.mvarId.replaceTargetEq rhs eqPrf)
        let goal := { goal with mvarId }
        if keepLooping then
          stepDirectivesLoop goal
        else
          return goal
      | none =>
        return goal

    let goal ← timed tStep <| withTraceNode `Kraken.kstep.phase (fun _ => return m!"step (dsimp + directives)") do
      stepDirectivesLoop goal
    goal.withContext do

    -- STEP 2: simp
    let (keepGoingSimp, goal) ← timed tSimp <| withTraceNode `Kraken.kstep.phase (fun _ => return m!"ksimp") <| Grind.liftGrindM $ do
      let simpResult ← Sym.simpGoal goal.mvarId simpMethods
      match simpResult with
      | .noProgress => pure (false, goal)
      | .goal mvarId => pure (true, { goal with mvarId })
      | .closed => throwError "kstep: unexpected closed goal during ksimp"

    -- STEP 3: spec lemmas
    let effectsAll ← do
      let goalT' ← instantiateMVars (← goal.mvarId.getType)
      let rec getEffectsAll (e : Expr) : Option Expr :=
        match e with
        | .letE _ _ _ body _ => getEffectsAll body
        | .mdata _ e => getEffectsAll e
        | _ =>
          if e.isAppOfArity ``Kraken.Effects.All 3 then
            some e
          else
            none
      let some effectsAll := getEffectsAll goalT' | return (goal, [])
      pure effectsAll

    let mctx ← getMCtx
    let m := Sym.getMatch mctx specTree effectsAll
    let specMatches := if m.isEmpty then Sym.getMatch mctx specTree effectsAll.appArg! else m

    let (keepGoingSpec, goal) ←
      match specMatches with
      | #[ thmName ] =>
        trace[Kraken.kstep] "Found a spec lemma: {thmName}"
        let (goal, subGoals) ← timed tSpec <| withTraceNode `Kraken.kstep.phase (fun _ => return m!"spec rewrite {thmName}") do
          rwTarget goal false (mkConst thmName)
        trace[Kraken.kstep] "{subGoals.length} subgoals generated"

        let solveIfNotAlready : Grind.Goal → Grind.GrindTacticM (Bool × Grind.Goal) := fun subGoal => do
          if ← subGoal.mvarId.isAssigned then
            return (false, subGoal)

          let subGoal ← subGoal.mvarId.withContext (preprocessGoalIfNeeded subGoal)
          let t ← subGoal.mvarId.getType
          unless ← subGoal.mvarId.withContext (isProp t) do
            return (false, subGoal)

          if t.getAppFn.isConstOf ``Std.ExtHashMap.sep then
            if ← ecancelGoal subGoal.mvarId then
              trace[Kraken.kstep] "Solved by ecancel: {t}"
              return (true, subGoal)

          let subGoal ← do
            let simpResult ← Grind.liftGrindM (Sym.simpGoal subGoal.mvarId simpMethods)
            match simpResult with
            | .noProgress => pure subGoal
            | .goal mvarId => pure { subGoal with mvarId }
            | .closed => pure subGoal
          if ← subGoal.mvarId.isAssigned then
            trace[Kraken.kstep] "Solved by ksimp: {t}"
            return (true, subGoal)

          if ← withReducible subGoal.mvarId.assumptionCore then
            let t ← instantiateMVars (← subGoal.mvarId.getType)
            let .some e ← getExprMVarAssignment? subGoal.mvarId | throwError "kstep: unassigned metavariable after assumptionCore"
            trace[Kraken.kstep] "Solved by exact: {t} by {e}"
            return (true, subGoal)

          let t ← instantiateMVars (← subGoal.mvarId.getType)
          if !t.hasExprMVar then
            try
              withReducible subGoal.mvarId.refl
              trace[Kraken.kstep] "Solved by refl: {t}"
              return (true, subGoal)
            catch _ => pure ()

            if ← subGoal.mvarId.withContext (isArithProp t) then
              if ← subGoal.mvarId.withContext (solveArithGoal subGoal.mvarId) then
                trace[Kraken.kstep] "Solved by omega: {t}"
                return (true, subGoal)
              if (← subGoal.mvarId.withContext (decideArithProp t)) == some false then
                trace[Kraken.kstep] "Refuted by omega (skipping grind): {t}"
                return (false, subGoal)

            let saved ← Grind.saveState
            try
              let cleanMVarId ← clearSepAndLets subGoal.mvarId (!isCalleeSavedEqType t)
              let g ← Grind.liftGrindM (Grind.mkGoal cleanMVarId)
              let g ← Grind.liftGrindM g.internalizeAll
              match ← Grind.liftGrindM g.grind with
              | .closed =>
                  trace[Kraken.kstep] "Solved by grind: {t}"
                  return (true, subGoal)
              | .failed _ =>
                  trace[Kraken.kstep] "NOT solved by grind: {t}"
                  saved.restore
                  return (false, subGoal)
            catch _ =>
              saved.restore
              return (false, subGoal)
          return (false, subGoal)

        let starGoal ← subGoals.findM? (fun (g : Grind.Goal) => do
          let t ← instantiateMVars (← g.mvarId.getType)
          if t.getAppFn.isConstOf ``Std.ExtHashMap.sep then
            trace[Kraken.kstep] "Found sep goal: {t}"
            return true
          else
            return false
        )

        let mut subGoals := subGoals
        if let some g := starGoal then
          let (solved, subGoals') ← timed tSpec do
            let addrGoal? ← subGoals.findM? fun (sg : Grind.Goal) => do
              if sg.mvarId == g.mvarId then return false
              let t ← instantiateMVars (← sg.mvarId.getType)
              unless t.isAppOfArity ``Eq 3 do return false
              return t.appArg!.isMVar
            let lenGoal? ← subGoals.findM? fun (sg : Grind.Goal) => do
              if sg.mvarId == g.mvarId then return false
              let t ← instantiateMVars (← sg.mvarId.getType)
              unless t.isAppOfArity ``Eq 3 do return false
              let lhs := t.appFn!.appArg!
              return lhs.isAppOfArity ``List.length 2 && lhs.appArg!.isMVar
            if let some addrGoal := addrGoal? then
              let addrGoalType ← instantiateMVars (← addrGoal.mvarId.getType)
              let addr := addrGoalType.appFn!.appArg!
              let addrMVar := addrGoalType.appArg!
              let candidates ← findSepAtCandidates g.mvarId
              let solveLenFast (lenGoal : Grind.Goal) : Grind.GrindTacticM Bool := do
                let lenGoal ← lenGoal.mvarId.withContext (preprocessGoalIfNeeded lenGoal)
                let simpResult ← Grind.liftGrindM (Sym.simpGoal lenGoal.mvarId simpMethods)
                let lenGoal ← match simpResult with
                  | .noProgress => pure lenGoal
                  | .goal mvarId => pure { lenGoal with mvarId }
                  | .closed => pure lenGoal
                if ← lenGoal.mvarId.isAssigned then return true
                if ← withReducible lenGoal.mvarId.assumptionCore then return true
                try
                  withReducible lenGoal.mvarId.refl
                  return true
                catch _ => pure ()
                lenGoal.mvarId.withContext (solveArithGoal lenGoal.mvarId)
              let tryAssignAndCancel (cand : SepAtCandidate) (hEq : Expr) : Grind.GrindTacticM Bool := do
                withConfig (fun c => { c with assignSyntheticOpaque := true }) do
                  -- Attempt 1: direct unsplit candidate `cand.bs`
                  let saved1 ← Grind.saveState
                  let ok1 ← try
                    unless ← isDefEq addrMVar cand.addr do failure
                    addrGoal.mvarId.assign hEq
                    unless ← solveSepAtCandidate g.mvarId cand none do failure
                    if let some lenGoal := lenGoal? then
                      unless ← solveLenFast lenGoal do
                        let (_, lenGoal') ← solveIfNotAlready lenGoal
                        unless ← lenGoal'.mvarId.isAssigned do failure
                    pure true
                  catch _ =>
                    saved1.restore
                    pure false
                  if ok1 then return true
                  -- Attempt 2: prefix split via `Mem.At_take_drop_sep` when `lenGoal?` is present
                  let some lenGoal := lenGoal? | return false
                  let saved2 ← Grind.saveState
                  let ok2 ← try
                    let lenType ← instantiateMVars (← lenGoal.mvarId.getType)
                    let wBytes := lenType.appArg!
                    let nExpr ← match ← (evalNat (← whnf wBytes)).run with
                      | some n => pure (mkNatLit n)
                      | none => pure wBytes
                    let (hSplit, hTakeLen) ← g.mvarId.withContext do
                      let splitFn ← mkAppM ``Mem.At_take_drop_sep #[cand.bs, nExpr, cand.addr]
                      let splitFnType ← inferType splitFn
                      let kType := splitFnType.bindingDomain!
                      let lenBoundType := splitFnType.bindingBody!.bindingDomain!
                      let some hBoth ← provePropGoal (mkAnd kType lenBoundType) | failure
                      let hK ← mkAppM ``And.left #[hBoth]
                      let hLen ← mkAppM ``And.right #[hBoth]
                      let hSplit := mkApp2 splitFn hK hLen
                      let hTakeLen ← mkAppM ``List.length_take_of_le #[hK]
                      pure (hSplit, hTakeLen)
                    unless ← isDefEq addrMVar cand.addr do failure
                    addrGoal.mvarId.assign hEq
                    unless ← solveSepAtCandidate g.mvarId cand (some hSplit) do failure
                    lenGoal.mvarId.withContext do
                      let expectedLenType ← instantiateMVars (← lenGoal.mvarId.getType)
                      let hTakeLen ← mkExpectedTypeHint hTakeLen expectedLenType
                      lenGoal.mvarId.assign hTakeLen
                    pure true
                  catch _ =>
                    saved2.restore
                    pure false
                  return ok2
              let dsimpAddr (e : Expr) : Grind.GrindTacticM Expr :=
                addrGoal.mvarId.withContext do
                  let e' ← expandLets e
                  let e' ← Grind.liftSymM (Sym.preprocessExpr e')
                  Grind.liftGrindM <|
                    Sym.dsimp (config := { maxSteps := 100000 })
                      (methods := { pre := dsimpCore })
                      e'
              let tryAssignSliceAndCancel (cand : SepAtCandidate) (off : Nat) (hEq : Expr) : Grind.GrindTacticM Bool := do
                withConfig (fun c => { c with assignSyntheticOpaque := true }) do
                  let some lenGoal := lenGoal? | return false
                  let saved ← Grind.saveState
                  try
                    let lenType ← instantiateMVars (← lenGoal.mvarId.getType)
                    let wBytes := lenType.appArg!
                    let nExpr ← match ← (evalNat (← whnf wBytes)).run with
                      | some n => pure (mkNatLit n)
                      | none => pure wBytes
                    let offExpr := mkNatLit off
                    let (hSplit, hTakeLen, targetAddr) ← g.mvarId.withContext do
                      let splitFn ← mkAppM ``Mem.At_slice_extract_sep #[cand.bs, offExpr, nExpr, cand.addr]
                      let splitFnType ← inferType splitFn
                      let sliceType := splitFnType.bindingDomain!
                      let lenBoundType := splitFnType.bindingBody!.bindingDomain!
                      let some hBoth ← provePropGoal (mkAnd sliceType lenBoundType) | failure
                      let hSlice ← mkAppM ``And.left #[hBoth]
                      let hLen ← mkAppM ``And.right #[hBoth]
                      let hSplit := mkApp2 splitFn hSlice hLen
                      let hTakeLen ← mkAppM ``Mem.length_drop_take_of_le #[cand.bs, offExpr, nExpr, hSlice]
                      let splitEqType ← instantiateMVars (← inferType hSplit)
                      let rhsArgs := splitEqType.appArg!.getAppArgs
                      let extractedClause := rhsArgs[rhsArgs.size - 2]!
                      let some (_, splitAddr) ← extractAtBytesAndAddr? extractedClause | failure
                      pure (hSplit, hTakeLen, splitAddr)
                    unless ← isDefEq addrMVar targetAddr do failure
                    addrGoal.mvarId.assign hEq
                    unless ← solveSepAtCandidate g.mvarId cand (some hSplit) do failure
                    lenGoal.mvarId.withContext do
                      let expectedLenType ← instantiateMVars (← lenGoal.mvarId.getType)
                      let hTakeLen ← mkExpectedTypeHint hTakeLen expectedLenType
                      lenGoal.mvarId.assign hTakeLen
                    pure true
                  catch _ =>
                    saved.restore
                    pure false
              let simplifyAddrEq (candAddr : Expr) : Grind.GrindTacticM (Expr × Grind.Goal) :=
                addrGoal.mvarId.withContext do
                  let eqType ← mkEq addr candAddr
                  let eqMVar ← mkFreshExprSyntheticOpaqueMVar eqType
                  let eqType' ← expandLets eqType
                  let eqType' ← Grind.liftSymM (Sym.preprocessExpr eqType')
                  let eqType' ← Grind.liftGrindM <|
                    Sym.dsimp (config := { maxSteps := 100000 })
                      (methods := { pre := dsimpCore })
                      eqType'
                  let mvarId ← eqMVar.mvarId!.replaceTargetDefEq eqType'
                  let eqGoal : Grind.Goal := { addrGoal with mvarId }
                  let eqGoal ← do
                    let r ← Grind.liftGrindM (Sym.simpGoal eqGoal.mvarId simpMethods)
                    match r with
                    | .noProgress => pure eqGoal
                    | .goal mvarId => pure { eqGoal with mvarId }
                    | .closed => pure eqGoal
                  pure (eqMVar, eqGoal)
              let trySliceAtOffset (cand : SepAtCandidate) (off : Nat) : Grind.GrindTacticM Bool := do
                let savedSlice ← Grind.saveState
                try
                  let sliceAddr ← addrGoal.mvarId.withContext do
                    let wOff ← mkAppM ``BitVec.ofNat #[mkNatLit 64, mkNatLit off]
                    mkAppM ``HAdd.hAdd #[cand.addr, wOff]
                  let fastEq? ← addrGoal.mvarId.withContext (tryProveBitVecAddEq addr sliceAddr)
                  let hEqS ← match fastEq? with
                    | some prf => pure prf
                    | none =>
                      let (eqMVarS, eqGoalS) ← simplifyAddrEq sliceAddr
                      if !(← eqGoalS.mvarId.isAssigned) then
                        eqGoalS.mvarId.withContext do
                          let eqT ← instantiateMVars (← eqGoalS.mvarId.getType)
                          if eqT.isAppOfArity ``Eq 3 then
                            let lhs := eqT.appFn!.appArg!
                            let rhs := eqT.appArg!
                            if let some prf ← tryProveBitVecAddEq lhs rhs then
                              eqGoalS.mvarId.assign prf
                      unless ← eqGoalS.mvarId.isAssigned do
                        discard <| proveBitVecEqByNorm eqGoalS.mvarId
                      unless ← eqGoalS.mvarId.isAssigned do
                        trace[Kraken.kstep] "slice grind on address equality: {← eqGoalS.mvarId.getType}"
                        let cleanMVarId ← clearSepAndLets eqGoalS.mvarId
                        let gS ← Grind.liftGrindM (Grind.mkGoal cleanMVarId)
                        let gS ← Grind.liftGrindM gS.internalizeAll
                        match ← Grind.liftGrindM gS.grind with
                        | .closed => pure ()
                        | .failed _ => failure
                      instantiateMVars eqMVarS
                  if ← tryAssignSliceAndCancel cand off hEqS then
                    pure true
                  else
                    savedSlice.restore
                    pure false
                catch _ =>
                  savedSlice.restore
                  pure false
              -- Pass 1: fast syntactic / reducible isDefEq / associative offset check
              let mut solvedSep := false
              for cand in candidates do
                unless solvedSep do
                  let saved ← Grind.saveState
                  try
                    if let some hEq ← addrGoal.mvarId.withContext (tryProveBitVecAddEq addr cand.addr) then
                      if ← tryAssignAndCancel cand hEq then
                        solvedSep := true
                      else
                        saved.restore
                    else
                      saved.restore
                  catch _ =>
                    saved.restore
              -- Pass 2: unfold local lets + dsimp/ksimp, then check if closed or reducible isDefEq
              let mut sliceCandidates : Array (SepAtCandidate × Nat) := #[]
              let mut skipGrindClauseIdxs : Array Nat := #[]
              unless solvedSep do
                let addrDsimp ← dsimpAddr addr
                let (lhsBaseDsimp, lhsOffDsimp) ← addrGoal.mvarId.withContext (peelBitVecAddSignedOffset addrDsimp)
                let lhsHasAddSub := hasAddOrSub lhsBaseDsimp
                for cand in candidates do
                  unless solvedSep do
                    let saved ← Grind.saveState
                    try
                      let candAddrDsimp ← dsimpAddr cand.addr
                      let (rhsBaseDsimp, rhsOffDsimp) ← addrGoal.mvarId.withContext (peelBitVecAddSignedOffset candAddrDsimp)
                      let sameBaseDsimp ← addrGoal.mvarId.withContext (withReducible (isDefEq lhsBaseDsimp rhsBaseDsimp))
                      if sameBaseDsimp && lhsOffDsimp != rhsOffDsimp then
                        saved.restore
                        skipGrindClauseIdxs := skipGrindClauseIdxs.push cand.clauseIdx
                        if lhsOffDsimp > rhsOffDsimp then
                          let off := (lhsOffDsimp - rhsOffDsimp).toNat
                          if canSliceCandidate cand off then
                            sliceCandidates := sliceCandidates.push (cand, off)
                      else if !sameBaseDsimp && !lhsHasAddSub && !hasAddOrSub rhsBaseDsimp then
                        saved.restore
                      else
                        if sameBaseDsimp && lhsOffDsimp == rhsOffDsimp then
                          if let some prfDsimp ← addrGoal.mvarId.withContext (tryProveBitVecAddEq addrDsimp candAddrDsimp) then
                            let hEq ← addrGoal.mvarId.withContext (mkExpectedTypeHint prfDsimp (← mkEq addr cand.addr))
                            if ← tryAssignAndCancel cand hEq then
                              solvedSep := true
                            else
                              saved.restore
                        unless solvedSep do
                          let (eqMVar, eqGoal) ← simplifyAddrEq cand.addr
                          if !(← eqGoal.mvarId.isAssigned) then
                            eqGoal.mvarId.withContext do
                              let eqT ← instantiateMVars (← eqGoal.mvarId.getType)
                              if eqT.isAppOfArity ``Eq 3 then
                                let lhs := eqT.appFn!.appArg!
                                let rhs := eqT.appArg!
                                if let some prf ← tryProveBitVecAddEq lhs rhs then
                                  eqGoal.mvarId.assign prf
                          let (sliceOffset?, sameBaseDiffOff) ←
                            if ← eqGoal.mvarId.isAssigned then
                              pure (none, false)
                            else
                              eqGoal.mvarId.withContext do
                                let eqT ← instantiateMVars (← eqGoal.mvarId.getType)
                                if eqT.isAppOfArity ``Eq 3 then
                                  let (lhsBase, lhsOff) ← peelBitVecAddSignedOffset eqT.appFn!.appArg!
                                  let (rhsBase, rhsOff) ← peelBitVecAddSignedOffset eqT.appArg!
                                  if lhsOff != rhsOff && (← withReducible (isDefEq lhsBase rhsBase)) then
                                    if lhsOff > rhsOff then
                                      pure (some (lhsOff - rhsOff).toNat, true)
                                    else
                                      pure (none, true)
                                  else
                                    pure (none, false)
                                else
                                  pure (none, false)
                          if !(← eqGoal.mvarId.isAssigned) && !sameBaseDiffOff then
                            discard <| proveBitVecEqByNorm eqGoal.mvarId
                          if ← eqGoal.mvarId.isAssigned then
                            let hEq ← instantiateMVars eqMVar
                            if ← tryAssignAndCancel cand hEq then
                              solvedSep := true
                            else
                              saved.restore
                          else
                            saved.restore
                            if sameBaseDiffOff then
                              skipGrindClauseIdxs := skipGrindClauseIdxs.push cand.clauseIdx
                            if let some off := sliceOffset? then
                              if canSliceCandidate cand off then
                                sliceCandidates := sliceCandidates.push (cand, off)
                    catch _ =>
                      saved.restore
              -- Pass 2b: try slicing multi-word candidates after exact-address candidates
              unless solvedSep do
                for (cand, off) in sliceCandidates do
                  unless solvedSep do
                    if ← trySliceAtOffset cand off then
                      solvedSep := true
              -- Pass 3: full grind on simplified address equality
              unless solvedSep do
                for cand in candidates do
                  unless solvedSep || skipGrindClauseIdxs.contains cand.clauseIdx do
                    let saved ← Grind.saveState
                    try
                      let (eqMVar, eqGoal) ← simplifyAddrEq cand.addr
                      unless ← eqGoal.mvarId.isAssigned do
                        discard <| proveBitVecEqByNorm eqGoal.mvarId
                      unless ← eqGoal.mvarId.isAssigned do
                        trace[Kraken.kstep] "Pass 3 grind on address equality: {← eqGoal.mvarId.getType}"
                        let cleanMVarId ← clearSepAndLets eqGoal.mvarId
                        let g ← Grind.liftGrindM (Grind.mkGoal cleanMVarId)
                        let g ← Grind.liftGrindM g.internalizeAll
                        match ← Grind.liftGrindM g.grind with
                        | .closed => pure ()
                        | .failed _ => failure
                      let hEq ← instantiateMVars eqMVar
                      if ← tryAssignAndCancel cand hEq then
                        solvedSep := true
                      else
                        saved.restore
                    catch _ =>
                      saved.restore
              pure (solvedSep, subGoals)
            else
              let (r, g') ← solveIfNotAlready g
              let subGoals' := subGoals.map fun sg => if sg.mvarId == g.mvarId then g' else sg
              pure (r, subGoals')
          subGoals := subGoals'
          if not solved then
            return (goal, subGoals)

        subGoals ← timed tSpec <| withTraceNode `Kraken.kstep.phase (fun _ => return m!"spec side goals") do
         let mut subGoals := subGoals
         while !(← subGoals.allM (·.mvarId.isAssigned)) do
          let mut progress := false
          let mut newSubGoals := []
          for subGoal in subGoals do
            let (r, subGoal') ← solveIfNotAlready subGoal
            progress := progress || r
            newSubGoals := newSubGoals ++ [subGoal']
          subGoals := newSubGoals
          unless progress do break
         pure subGoals

        let unsolvedGoals ← subGoals.filterMapM fun (g : Grind.Goal) => do
          if ← g.mvarId.isAssigned then
            return none
          else
            return some g
        unsolvedGoals.forM fun mvarId => do
          let t ← mvarId.mvarId.getType
          trace[Kraken.kstep] "Unsolved goal: {t}"
        if unsolvedGoals.length > 0 then
          return (goal, unsolvedGoals)

        pure (true, goal)
      | #[] =>
        pure (false, goal)
      | _ =>
        throwError "kstep: multiple @[kspec] lemmas matched goal"

    let (keepGoingIte, goal) ← timed tIte do
      if !keepGoingSimp && !keepGoingSpec && effectsAll.appArg!.isAppOfArity ``ite 5 then
        let iteExpr := effectsAll.appArg!
        let _α := iteExpr.getArg! 0
        let c := iteExpr.getArg! 1
        let inst := iteExpr.getArg! 2
        let t := iteExpr.getArg! 3
        let f := iteExpr.getArg! 4
        let notC := mkNot c
        let MD := effectsAll.getArg! 0
        let post := effectsAll.getArg! 1
        let allFn := effectsAll.getAppFn
        let takeTrue (hc : Expr) : Grind.GrindTacticM (Bool × Grind.Goal) := do
          let eqPrf := mkAppN (mkConst ``Effects_All_ite_true) #[MD, post, c, inst, hc, t, f]
          let rhs ← Grind.liftSymM (Sym.preprocessExpr (mkAppN allFn #[MD, post, t]))
          let mvarId ← goal.mvarId.replaceTargetEq rhs eqPrf
          pure (true, { goal with mvarId })
        let takeFalse (hnc : Expr) : Grind.GrindTacticM (Bool × Grind.Goal) := do
          let eqPrf := mkAppN (mkConst ``Effects_All_ite_false) #[MD, post, c, inst, hnc, t, f]
          let rhs ← Grind.liftSymM (Sym.preprocessExpr (mkAppN allFn #[MD, post, f]))
          let mvarId ← goal.mvarId.replaceTargetEq rhs eqPrf
          pure (true, { goal with mvarId })
        if let some hc ← goal.mvarId.withContext (assumptionModBool c) then
          trace[Kraken.kstep] "ite condition by assumption: {c}"
          takeTrue hc
        else if let some hnc ← goal.mvarId.withContext (assumptionModBool notC) then
          trace[Kraken.kstep] "ite negated condition by assumption: {notC}"
          takeFalse hnc
        else
          let tryProveIteCondSlow (prop : Expr) : Grind.GrindTacticM (Option Expr) :=
            goal.mvarId.withContext do
              trace[Kraken.kstep.phase] "ite condition: {prop}"
              let saved ← Grind.saveState
              try
                let mvar ← mkFreshExprSyntheticOpaqueMVar prop
                let prop' ← expandLets prop
                let prop' ← Grind.liftSymM (Sym.preprocessExpr prop')
                let prop' ← Grind.liftGrindM <|
                  Sym.dsimp (config := { maxSteps := 100000 })
                    (methods := { pre := evalGround >> kdsimpDecls >> kdsimpMatch >> kdsimpProj >> kbeta })
                    prop'
                let mvarId ← mvar.mvarId!.replaceTargetDefEq prop'
                let mvarId ← do
                  let r ← Grind.liftGrindM (Sym.simpGoal mvarId simpMethods)
                  match r with
                  | .noProgress => pure mvarId
                  | .goal mvarId => pure mvarId
                  | .closed => pure mvarId
                unless ← mvarId.isAssigned do
                  try
                    withReducible mvarId.refl
                  catch _ => pure ()
                let mvarId ← do
                  if ← mvarId.isAssigned then pure mvarId else
                  match ← mvarId.withContext (simpWithHyps mvarId) with
                  | .closed => pure mvarId
                  | .refuted => failure
                  | .goal m => pure m
                unless ← mvarId.isAssigned do
                  let curType ← mvarId.getType
                  if ← mvarId.withContext (isArithProp curType) then
                    if ← solveArithGoal mvarId then
                      trace[Kraken.kstep] "ite condition by omega"
                    else if (← mvarId.withContext (decideArithProp curType)) == some false then
                      failure
                unless ← mvarId.isAssigned do
                  trace[Kraken.kstep] "ite grind on: {← mvarId.getType}"
                  let cleanMVarId ← clearSepAndLets mvarId false
                  let g ← Grind.liftGrindM (Grind.mkGoal cleanMVarId)
                  let g ← Grind.liftGrindM g.internalizeAll
                  match ← Grind.liftGrindM g.grind with
                  | .closed => pure ()
                  | .failed _ => failure
                let prf ← instantiateMVars mvar
                return some prf
              catch _ =>
                saved.restore
                return none
          if t.getAppFn.isConstOf ``Kraken.Effects.undefined ||
             t.getAppFn.isConstOf ``Kraken.Effects.unaligned ||
             t.getAppFn.isConstOf ``Kraken.Effects.unimplemented then
            if let some hnc ← tryProveIteCondSlow notC then
              takeFalse hnc
            else if let some hc ← tryProveIteCondSlow c then
              takeTrue hc
            else
              pure (false, goal)
          else
            if let some hc ← tryProveIteCondSlow c then
              takeTrue hc
            else if let some hnc ← tryProveIteCondSlow notC then
              takeFalse hnc
            else
              pure (false, goal)
      else
        pure (false, goal)

    trace[Kraken.kstep] "kstep: keepGoing = {keepGoingSimp}"

    if keepGoingSimp || keepGoingSpec || keepGoingIte then
      go goal
    else
      pure (goal, [])

  let (goal, subGoals) ← go goal

  trace[Kraken.kstep] "END KSTEP: {subGoals.length} sub-goals left"
  trace[Kraken.kstep.phase] "kstep time (ms): preprocess {(← tPre.get) / 1000000}, step {(← tStep.get) / 1000000}, ksimp {(← tSimp.get) / 1000000}, spec {(← tSpec.get) / 1000000}, ite {(← tIte.get) / 1000000}"

  if let .some r := maxInstrCount then
    let remaining ← r.get
    if remaining > 0 then
      throwError m!"kstep could not step through the remaining {remaining} steps"

  Grind.setGoals (subGoals ++ [ goal ])

syntax (name := symRotateRight) "rotate_right" (ppSpace num)? : grind

@[grind_tactic symRotateRight]
def evalSymRotateRight : Grind.GrindTactic := fun stx => do
  let n := if stx[1].isNone then 1 else stx[1][0].toNat
  let goals ← Grind.getGoals
  Grind.setGoals (goals.rotateRight n)

@[tactic tacticKStep]
def evalTacticKStep : Tactic := fun stx => withMainContext do
  let `(tactic| kstep $cfg:optConfig $[$n:num]?) := stx | throwUnsupportedSyntax
  let step ← `(grind| kstep $cfg:optConfig $[$n:num]?)
  let goal ← getMainGoal
  let params ← Grind.mkDefaultParams { clean := false }
  let (_, state) ← Grind.GrindTacticM.runAtGoal goal params (sym := true) do
    unless (← Grind.getUnsolvedGoals).isEmpty do
      Grind.evalGrindTactic step
  replaceMainGoal (state.goals.map (·.mvarId))

end
