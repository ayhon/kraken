module

public import Kraken.Frame
public import Kraken.OmniSemantics
public meta import Lean.Elab.Command

/-!
# Block and Function Specification DSL (`block_spec`)

Command macro for declaring composable block and function specifications (`Executable.Spec`)
with concise `from`, `to`/`exit`, `writes`/`preserves`, `ct`/`trace`, `pre`, and `post` clauses.

```lean
block_spec step_block prog s₀ (R : DataMem → Prop)
  from "entry" to "done"
  (writes := [X0, X1])
  (pre := s₀.regs.X0 = 0)
  (post := fun st => st.data.dmem = s₀.dmem) := by
  …
```
expands to

```lean
theorem step_block [layout : Host prog] (s₀ : MachineData)
    (R : DataMem → Prop) :
    (layout prog).Spec s₀
      (pc := (layout prog).label "entry")
      (pre := s₀.regs.X0 = 0)
      (post := fun st =>
        st.pc = (layout prog).label "done" ∧
        st.data.regs ≡ s₀.regs except [X0, X1] ∧
        st.data.dmem = s₀.dmem) := by
  …
```

* `from` (entry label) is optional: without it the block starts at the program's start address.
* `to "label"` or `(exit := e)` give the program counter of the final state; without either the
  post has no `pc` conjunct.
* `(writes := [r, …])` adds the frame conjunct `st.data.regs ≡ s₀.regs except [r, …]`
  (`(writes := [])` means no register is modified), where each entry may be a register name or a
  view on the register file (expanded to the registers it reads).
* `(preserves := [r, …])` adds the dual frame conjunct `st.data.regs ≡ s₀.regs on [r, …]`,
  where each entry may be a register name or a derived view on the register file.
* `ct` states an existential constant-time specification
  `∃ tr, ∀ (s₀ : MachineData) …, Spec … (trace := some tr) …` (binders placed before `s₀` are
  public parameters outside `∃ tr`; binders after `s₀` are secret parameters inside `∀ s₀`).
  `(trace := tr)` supplies an explicit trace term `tr`.
* `(post := fun st => …)` is mandatory; `(pre := …)` is optional.
-/

public meta section

open Lean Meta Elab

syntax blockSpecFrom := &"from " str
syntax blockSpecTo := &"to " str
syntax blockSpecExit := atomic("(" &"exit" " := ") term ")"
syntax blockSpecWrites := atomic("(" &"writes" " := ") "[" ident,* "]" ")"
syntax blockSpecPreserves := atomic("(" &"preserves" " := ") "[" ident,* "]" ")"
syntax blockSpecTrace := atomic("(" &"trace" " := ") term ")"
syntax blockSpecCt := &"ct"
syntax blockSpecPre := atomic("(" &"pre" " := ") term ")"
syntax blockSpecPost := atomic("(" &"post" " := ") term ")"

/-- Typed explicit `(x y : T)`, implicit `{x y : T}`, or instance `[T]` / `[inst : T]` binders,
so that `(name := …)` options cannot be mistaken for binders with default values. -/
syntax blockSpecExplicitBinder := atomic("(" ident+ " : ") term ")"
syntax blockSpecImplicitBinder := "{" ident+ (" : " term)? "}"
syntax blockSpecInstBinder := "[" (atomic(ident " : "))? term "]"
syntax blockSpecBinder := blockSpecExplicitBinder <|> blockSpecImplicitBinder <|> blockSpecInstBinder

private def elabBlockSpecBinder (b : TSyntax ``blockSpecBinder) :
    MacroM (TSyntax ``Lean.Parser.Term.bracketedBinder) := do
  let inner := b.raw[0]
  if inner.isOfKind ``blockSpecExplicitBinder then
    let xs : TSyntaxArray `ident := inner[1].getArgs.map (⟨·⟩)
    let t : Term := ⟨inner[3]⟩
    `(bracketedBinder| ($xs* : $t))
  else if inner.isOfKind ``blockSpecImplicitBinder then
    let xs : TSyntaxArray `ident := inner[1].getArgs.map (⟨·⟩)
    if inner[2].isNone then
      `(bracketedBinder| {$xs*})
    else
      let t : Term := ⟨inner[2][1]⟩
      `(bracketedBinder| {$xs* : $t})
  else if inner.isOfKind ``blockSpecInstBinder then
    if inner[1].isNone then
      let t : Term := ⟨inner[2]⟩
      `(bracketedBinder| [$t])
    else
      let x : Ident := ⟨inner[1][0]⟩
      let t : Term := ⟨inner[2]⟩
      `(bracketedBinder| [$x : $t])
  else
    Macro.throwUnsupported

syntax (name := blockSpec) declModifiers "block_spec " ident ident
  blockSpecBinder* ident blockSpecBinder*
  (blockSpecFrom)? (blockSpecTo <|> blockSpecExit)?
  (blockSpecTrace <|> blockSpecCt)? (blockSpecWrites <|> blockSpecPreserves)?
  (blockSpecTrace <|> blockSpecCt)? (blockSpecPre)? blockSpecPost " := " term : command

macro_rules
  | `($mods:declModifiers block_spec $name:ident $prog:ident
      $pubBs:blockSpecBinder* $s:ident $secBs:blockSpecBinder*
      $[$from?]? $[$exit?]? $[$trace1?]? $[$frame?]? $[$trace2?]? $[$pre?]? (post := $post) := $proof) => do
    let trace? := trace1?.orElse (fun () => trace2?)
    let host := mkIdent `Host
    let layout := mkIdent `layout
    let machineData := mkIdent `MachineData
    let (st, postBody) : Ident × Term ← match post with
      | `(fun $x:ident => $body) => pure (x, body)
      | `(fun ($x:ident : $_) => $body) => pure (x, body)
      | _ => do
        let st := mkIdent `st
        pure (st, ← `(($post) $st))
    let pubBinders ← pubBs.mapM elabBlockSpecBinder
    let secBinders ← secBs.mapM elabBlockSpecBinder
    let mut conj : Array Term := #[]
    if let some ex := exit? then
      match ex with
      | `(blockSpecTo| to $l:str) => conj := conj.push (← `($(st).pc = ($layout $prog).label $l))
      | `(blockSpecExit| (exit := $e)) => conj := conj.push (← `($(st).pc = $e))
      | _ => Macro.throwUnsupported
    if let some fr := frame? then
      match fr with
      | `(blockSpecWrites| (writes := [$rs:ident,*])) =>
        conj := conj.push (← `($(st).data.regs ≡ $(s).regs except [$rs,*]))
      | `(blockSpecPreserves| (preserves := [$rs:ident,*])) =>
        conj := conj.push (← `($(st).data.regs ≡ $(s).regs on [$rs,*]))
      | _ => Macro.throwUnsupported
    conj := conj.push postBody
    let body ← conj.pop.foldrM (init := conj.back!) fun c acc => `($c ∧ $acc)
    let postFn ← `(fun $st => $body)
    let pcTerm : Term ← match from? with
      | some f => match f with
        | `(blockSpecFrom| from $l:str) => `(($layout $prog).label $l)
        | _ => Macro.throwUnsupported
      | none => `(($layout $prog).startAddr)
    let preTerm : Term ← match pre? with
      | some pr => match pr with
        | `(blockSpecPre| (pre := $p)) => pure p
        | _ => Macro.throwUnsupported
      | none => `(True)
    match trace? with
    | some t =>
      match t with
      | `(blockSpecCt| ct) =>
        let tr := mkIdent `tr
        `($mods:declModifiers theorem $name [$layout : $host $prog] $pubBinders* :
            ∃ $tr:ident, ∀ ($s : $machineData) $secBinders*,
              Kraken.Executable.Spec ($layout $prog) $s $pcTerm (some $tr) $preTerm $postFn := $proof)
      | `(blockSpecTrace| (trace := $tr)) =>
        `($mods:declModifiers theorem $name [$layout : $host $prog] $pubBinders*
            ($s : $machineData) $secBinders* :
            Kraken.Executable.Spec ($layout $prog) $s $pcTerm (some $tr) $preTerm $postFn := $proof)
      | _ => Macro.throwUnsupported
    | none =>
      `($mods:declModifiers theorem $name [$layout : $host $prog] $pubBinders*
          ($s : $machineData) $secBinders* :
          Kraken.Executable.Spec ($layout $prog) $s $pcTerm none $preTerm $postFn := $proof)

end
