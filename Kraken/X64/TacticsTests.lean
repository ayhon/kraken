module

import Kraken.Tactics
import Kraken.X64.OmniSemantics
import Kraken.X64.Semantics

private def kprologueTestProgram : Program := []

-- The hygienic state alias must not capture an existing `ss`.
example [layout : Layout] (P : Prop) (ss : Nat) (s : MachineData) (hP : P) :
    straightlineStep (layout kprologueTestProgram) ⟨s, layout.start⟩ (fun _ => P) := by
  kprologue
  have _ : Program := prog
  have _ : Nat := ss
  have _ : UInt64 := r15
  have _ : RegZmms := zmms
  have _ : StatusFlags := flags
  have _ : DataMem := mem
  sym => kstep; tactic => exact hP

-- `kprologue as <ident>` binds the program under the given name.
example [layout : Layout] (P : Prop) (prog : Nat) (s : MachineData) (hP : P) :
    straightlineStep (layout (kprologueTestProgram ++ kprologueTestProgram)) ⟨s, layout.start⟩ (fun _ => P) := by
  kprologue as myProg
  have _ : Nat := prog
  have _ : Program := myProg
  sym => kstep; tactic => exact hP

/--
error: kprologue: duplicate local names: rax
-/
#guard_msgs in
example [layout : Layout] (s : MachineData) :
    straightlineStep (layout kprologueTestProgram) ⟨s, layout.start⟩ (fun _ => True) := by
  kprologue as rax

/--
error: kprologue: refusing to shadow existing locals: rax
-/
#guard_msgs in
example [layout : Layout] (rax : UInt64) (s : MachineData) :
    straightlineStep (layout kprologueTestProgram) ⟨s, layout.start⟩ (fun _ => True) := by
  kprologue

/--
error: kprologue: refusing to shadow existing locals: myProg
-/
#guard_msgs in
example [layout : Layout] (myProg : Nat) (s : MachineData) :
    straightlineStep (layout kprologueTestProgram) ⟨s, layout.start⟩ (fun _ => True) := by
  kprologue as myProg
