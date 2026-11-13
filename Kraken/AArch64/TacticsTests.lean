module

import Kraken.AArch64.Semantics
import Kraken.Tactics

/-!
# AArch64 Tactic Tests (`kprologue`)

Hygiene and local-shadowing regression tests for `kprologue` on AArch64 machine states.
-/

/-! ### `kprologue` State Destructuring and Hygiene -/

private def kprologueTestProgram : Program := []

-- The hygienic state alias must not capture an existing `ss`.
example [layout : Host kprologueTestProgram] (P : Prop) (ss : Nat) (s : MachineData) (hP : P) :
    Eventually (step1 (layout kprologueTestProgram)) (fun _ => P) ⟨s, layout.start⟩ := by
  kprologue kprologueTestProgram with s
  have _ : Nat := ss
  have _ : UInt64 := X30
  have _ : UInt64 := SP
  have _ : StatusFlags := flags
  have _ : DataMem := mem
  exact Eventually.done _ hP

/--
error: kprologue: refusing to shadow existing locals: X0
-/
#guard_msgs in
example [layout : Host kprologueTestProgram] (X0 : UInt64) (s : MachineData) :
    Eventually (step1 (layout kprologueTestProgram)) (fun _ => True) ⟨s, layout.start⟩ := by
  kprologue kprologueTestProgram with s
