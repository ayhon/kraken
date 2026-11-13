module

import Kraken.AArch64.Parser
import Kraken.AArch64.Semantics
import Kraken.Tactics

/-!
# AArch64 Composition and Frame Tactic Tests

Regression tests for `kcall`, `kloop`, `kloop_exit`, `kloop_next`, `kframe`, `kframe_eqs`,
`≡ … except`, and `block_spec` on AArch64 examples.
-/

open Kraken Kraken.AArch64
open Kraken.AArch64.Parser

/-! ### Frame Clauses and `kframe_eqs` -/

/-- Multi-register branch program for testing register frames and register-view projections. -/
def check_zero_branch : Program := ⸨prog|
loop:
  orr x14, x25, x26
  rbit x15, x25
  cbz x14, loop_end
  clz x13, x15
shift:
  nop
loop_end:
  nop
⸩

/-- Register-tuple projections for testing view expansion in `kframe`, `kframe_eqs`, and `≡ … except`. -/
abbrev Reg64s.viewB (r : Reg64s) : Nat := r.X25.toNat + r.X26.toNat
abbrev Reg64s.viewA (r : Reg64s) : Nat := r.X21.toNat + r.X22.toNat
abbrev Reg64s.viewX (r : Reg64s) : Nat :=
  r.X3.toNat + r.X4.toNat + r.X5.toNat + r.X6.toNat + r.X7.toNat
abbrev Reg64s.viewY (r : Reg64s) : Nat := r.X8.toNat + r.X9.toNat

/-- Block lemma with a register-frame (`≡ … except […]`) postcondition. -/
theorem loop_exit_frame [layout : Host check_zero_branch]
    (s₀ : MachineData) :
    (layout check_zero_branch).Spec s₀
      (pc := (layout check_zero_branch).label "loop")
      (pre := s₀.regs.viewB = 0)
      (post := fun st =>
        st.pc = (layout check_zero_branch).label "loop_end" ∧
        st.data.regs ≡ s₀.regs except [X14, X15] ∧
        st.data.dmem = s₀.dmem) := by
  intro h_B_zero
  dsimp only [Reg64s.viewB] at h_B_zero
  have h25 : s₀.regs.X25.toBitVec = 0#64 := BitVec.eq_of_toNat_eq (by simp; omega)
  have h26 : s₀.regs.X26.toBitVec = 0#64 := BitVec.eq_of_toNat_eq (by simp; omega)
  kprologue check_zero_branch at "loop" to "shift" with s₀
  kfinish check_zero_branch

/-- Composing a frame lemma with `kcall` and deriving register-view equalities via `kframe_eqs`. -/
example [layout : Host check_zero_branch] (s : MachineData)
    (hB : s.regs.viewB = 0) :
    (layout check_zero_branch).Spec s
      (pc := (layout check_zero_branch).label "loop")
      (post := fun st =>
        st.pc = (layout check_zero_branch).label "loop_end" ∧
        st.data.regs ≡ s.regs except [X14, X15, X13] ∧
        st.data.regs.viewA = s.regs.viewA) := by
  intro _
  kcall loop_exit_frame s hB with st1 ⟨h1_fr, h1_mem⟩
  kframe_eqs h1_fr
  apply Eventually.done
  refine ⟨rfl, ?_, ?_⟩
  · kframe
  · exact h1_fr_viewA

/-! ### `kstep` Bitfield and Shift Normalization -/

/-- `extr`, `lsr #k`, and `ubfx` normalize to shift/extract expressions during `kstep`. -/
def extr_lsr : Program := ⸨prog|
  extr x0, x1, x2, #1
  lsr  x4, x3, #5
  ubfx x5, x3, #8, #16
⸩

theorem extr_lsr_correct [layout : Host extr_lsr] (s₀ : MachineData) :
    (layout extr_lsr).Spec s₀
      (post := fun st =>
        st.data.regs.X0.toBitVec = s₀.regs.X1.toBitVec <<< 63 ||| s₀.regs.X2.toBitVec >>> 1 ∧
        st.data.regs.X4.toBitVec = s₀.regs.X3.toBitVec >>> 5 ∧
        st.data.regs.X5.toBitVec =
          BitVec.setWidth 64 (BitVec.extractLsb' 0 16 (s₀.regs.X3.toBitVec >>> 8)) ∧
        st.data.regs ≡ s₀.regs except [X0, X4, X5]) := by
  kprologue extr_lsr with s₀
  kfinish extr_lsr

/-! ### Flag Abstraction Boundary -/

/-- `subs` leaves `status := StatusFlags.subs a b` in the state; `b.lo` is decided via `@[kcond]`. -/
def cmp_branch : Program := ⸨prog|
  subs x2, x0, x1
  b.lo less
  mov x3, #1
  b done
less:
  mov x3, #0
done:
  nop
⸩

theorem cmp_branch_correct [layout : Host cmp_branch] (s₀ : MachineData) :
    (layout cmp_branch).Spec s₀
      (post := fun st =>
        st.data.regs.X3.toNat = (if s₀.regs.X0.toNat < s₀.regs.X1.toNat then 0 else 1) ∧
        st.data.status = StatusFlags.subs s₀.regs.X0.toBitVec s₀.regs.X1.toBitVec ∧
        st.data.regs ≡ s₀.regs except [X2, X3]) := by
  kprologue cmp_branch with s₀
  by_cases h : X0.toNat < X1.toNat
  · kstep
    kprologue cmp_branch at "less"
    kfinish cmp_branch
  · kstep
    kprologue cmp_branch at "done"
    kfinish cmp_branch

/-! ### `block_spec` Declarations and Frame Narrowing -/

/-- `block_spec` with `writes` expands to the exact `Spec` signature of `loop_exit_frame`. -/
block_spec loop_exit_spec check_zero_branch s₀
  from "loop" to "loop_end"
  (writes := [X14, X15])
  (pre := s₀.regs.viewB = 0)
  (post := fun st => st.data.dmem = s₀.dmem) := by
  intro h_B_zero
  dsimp only [Reg64s.viewB] at h_B_zero
  have h25 : s₀.regs.X25.toBitVec = 0#64 := BitVec.eq_of_toNat_eq (by simp; omega)
  have h26 : s₀.regs.X26.toBitVec = 0#64 := BitVec.eq_of_toNat_eq (by simp; omega)
  kprologue check_zero_branch at "loop" to "shift" with s₀
  kfinish check_zero_branch

example : @loop_exit_spec = @loop_exit_frame := rfl

/-- Whole-program `block_spec` with implicit/explicit binders and `ct` constant-time mode. -/
block_spec extr_lsr_correct' extr_lsr {n : Nat} s₀ ct
  (writes := [X0, X4, X5])
  (pre := n = 5)
  (post := fun st =>
    st.data.regs.X0.toBitVec = s₀.regs.X1.toBitVec <<< 63 ||| s₀.regs.X2.toBitVec >>> 1 ∧
    st.data.regs.X4.toBitVec = s₀.regs.X3.toBitVec >>> n) := by
  kprologue extr_lsr with s₀
  kfinish extr_lsr

/-- Narrowing an `except` frame into a `preserves` (`≡ … on […]`) frame over registers and views. -/
block_spec loop_exit_preserves check_zero_branch s
  from "loop" to "loop_end"
  (preserves := [SP, X29, viewA, viewY])
  (pre := s.regs.viewB = 0)
  (post := fun st => st.data.dmem = s.dmem) := by
  intro hB
  kcall loop_exit_spec s hB with st1 ⟨h1_fr, h1_mem⟩
  apply Eventually.done
  exact ⟨rfl, by kframe, h1_mem⟩

-- Register views in `≡ … except […]` expand to the underlying registers they read.
example (r' r : Reg64s) :
    (r' ≡ r except [viewX, X13]) = (r' ≡ r except [X3, X4, X5, X6, X7, X13]) := rfl

/-! ### `kloop` with 1-Argument Exit Predicate -/

/-- Loop with prologue, body, and epilogue handled in a single `kloop` call. -/
def count_down_epilogue : Program := ⸨prog|
  mov x0, #0
  cbz x1, done
loop:
  add x0, x0, #1
  sub x1, x1, #1
  cbnz x1, loop
done:
  add x0, x0, #10
⸩

block_spec count_down_epilogue_correct count_down_epilogue (n : Nat) s₀
  (writes := [X0, X1])
  (pre := s₀.regs.X1.toNat = n)
  (post := fun st => st.data.regs.X0.toBitVec = BitVec.ofNat 64 (n + 10)) := by
  intro h_x1
  kloop at "loop" (writes := [X0, X1])
    (inv := fun v (k : Nat) st =>
      0 < v ∧
      v + k = n ∧
      st.data.regs.X1.toNat = v ∧
      st.data.regs.X0.toBitVec = BitVec.ofNat 64 k)
    (exit := fun st =>
      st.pc = (layout count_down_epilogue).label "done" ∧
      st.data.regs ≡ s₀.regs except [X0, X1] ∧
      st.data.regs.X0.toBitVec = BitVec.ofNat 64 n)
    (measure := n)
    (ghost := (0 : Nat))
    with v k ⟨hv, hvk, h_x1_v, h_x0_v⟩
  · kprologue count_down_epilogue to "loop" with s₀
    by_cases hn : n = 0
    · subst hn
      kloop_exit
      kfinish count_down_epilogue
    · kloop_next
      kfinish count_down_epilogue
  · kprologue count_down_epilogue at "loop" to "done" with st
    by_cases hv1 : v = 1
    · subst hv1
      kloop_exit
      kfinish count_down_epilogue
    · kloop_next (v - 1) (k + 1)
      kfinish count_down_epilogue
  · obtain ⟨h_fr_done, h_x0_done⟩ := hst
    kframe_eqs h_fr_done
    kprologue count_down_epilogue at "done" with st
    kfinish count_down_epilogue


