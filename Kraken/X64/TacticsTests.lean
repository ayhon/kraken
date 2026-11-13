module

import Kraken.Tactics
import Kraken.X64.Semantics

/-!
# x86-64 Tactic Tests (`kprologue`)

Hygiene and local-shadowing regression tests for `kprologue` on x86-64 machine states.
-/

/-! ### `kprologue` State Destructuring and Hygiene -/

private def kprologueTestProgram : Program := []

-- The hygienic state alias must not capture an existing `ss`.
example [layout : Host kprologueTestProgram] (P : Prop) (ss : Nat) (s : MachineData) (hP : P) :
    Eventually (step1 (layout kprologueTestProgram)) (fun _ => P) ⟨s, layout.start⟩ := by
  kprologue kprologueTestProgram with s
  have _ : Nat := ss
  have _ : UInt64 := r15
  have _ : RegZmms := zmms
  have _ : StatusFlags := flags
  have _ : DataMem := mem
  exact Eventually.done _ hP

/--
error: kprologue: refusing to shadow existing locals: rax
-/
#guard_msgs in
example [layout : Host kprologueTestProgram] (rax : UInt64) (s : MachineData) :
    Eventually (step1 (layout kprologueTestProgram)) (fun _ => True) ⟨s, layout.start⟩ := by
  kprologue kprologueTestProgram with s
