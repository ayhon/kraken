module

import Kraken.AArch64.Parser
import Kraken.AArch64.Semantics
import Kraken.BitVecArith
import Kraken.SeparationMem
import Kraken.SeparationTactics
import Kraken.Tactics
import Kraken.ToBytes

/-!
# AArch64 `memcpy` Verification

Functional correctness of AAPCS64 `memcpy(dst, src, n)`.
-/

open Kraken.AArch64
open Kraken.AArch64.Parser
open Std.ExtHashMap

/-- AAPCS64 `memcpy(dst, src, n)`:
- Arguments: `x0 = dst`, `x1 = src`, `x2 = n`, `x30 (lr) = ra`
- Returns: `x0 = dst`, `sp = sp₀`, `pc = x30₀`, callee-saved registers preserved,
  and `src` bytes copied into `dst`. -/
def memcpy : Program := ⸨prog|
memcpy:
  mov x3, x0
  cbz x2, done
loop:
  ldrb w4, [x1]
  strb w4, [x3]
  add x1, x1, #1
  add x3, x3, #1
  sub x2, x2, #1
  cbnz x2, loop
done:
  ret
⸩

theorem memcpy_correct [layout : Host memcpy] (s₀ : MachineData)
    (n : Nat) (dst src : List UInt8) (R : DataMem → Prop) :
    (layout memcpy).Spec s₀
      (pre :=
        s₀.regs.X2.toNat = n ∧
        dst.length = n ∧
        src.length = n ∧
        (s₀.dmem =⋆ dst @ s₀.regs.X0 ⋆ src @ s₀.regs.X1 ⋆ R))
      (post := fun st =>
        st.pc = Int64.ofBitVec s₀.regs.X30.toBitVec ∧
        st.data.regs.X0 = s₀.regs.X0 ∧
        st.data.regs.SP = s₀.regs.SP ∧
        st.data.regs.CalleeSavedEq s₀.regs ∧
        (st.data.dmem =⋆ src @ s₀.regs.X0 ⋆ src @ s₀.regs.X1 ⋆ R)) := by
  rintro ⟨h_x2, h_dst_len, h_src_len, h_mem⟩
  kloop at "loop"
    (inv := fun v (dst_ptr, src_ptr, dst_bs, src_bs, frame) st =>
      0 < v ∧
      st.data.regs.X2.toNat = v ∧
      st.data.regs.X3.toBitVec = dst_ptr ∧
      st.data.regs.X1.toBitVec = src_ptr ∧
      st.data.regs.X0 = s₀.regs.X0 ∧
      st.data.regs.X30 = s₀.regs.X30 ∧
      st.data.regs.SP = s₀.regs.SP ∧
      st.data.regs.CalleeSavedEq s₀.regs ∧
      dst_bs.length = v ∧
      src_bs.length = v ∧
      (st.data.dmem =⋆ dst_bs @ dst_ptr ⋆ src_bs @ src_ptr ⋆ frame))
    (exit := fun _ (dst_ptr, src_ptr, _, src_bs, frame) st =>
      st.pc = (layout memcpy).label "done" ∧
      st.data.regs.X0 = s₀.regs.X0 ∧
      st.data.regs.X30 = s₀.regs.X30 ∧
      st.data.regs.SP = s₀.regs.SP ∧
      st.data.regs.CalleeSavedEq s₀.regs ∧
      (st.data.dmem =⋆ src_bs @ dst_ptr ⋆ src_bs @ src_ptr ⋆ frame))
    (measure := n)
    (ghost := (s₀.regs.X0.toBitVec, s₀.regs.X1.toBitVec, dst, src, R))
    with v ⟨dst_ptr, src_ptr, dst_bs, src_bs, frame⟩
      ⟨hv, h_x2_v, rfl, rfl, h_x0, h_x30, h_sp, h_cs, h_dst_v, h_src_v, h_mem_v⟩
  · kprologue memcpy to "loop"
    by_cases hn : n = 0
    · subst hn
      obtain rfl := List.eq_nil_of_length_eq_zero h_dst_len
      obtain rfl := List.eq_nil_of_length_eq_zero h_src_len
      kloop_exit
      kfinish memcpy
    · kloop_next
      kfinish memcpy
  · by_cases hv1 : v = 1
    · subst hv1
      kprologue memcpy at "loop" to "done" with st
      kloop_exit
      kfinish memcpy
    · kprologue memcpy at "loop" to "done" with st
      kloop_next (v - 1) (X3.toBitVec + 1#64, X1.toBitVec + 1#64, dst_bs.drop 1, src_bs.drop 1,
        (src_bs.take 1) @ X3 ⋆ (src_bs.take 1) @ X1 ⋆ frame)
      · kfinish memcpy
      · rintro t_s ⟨hQ_pc, hQ_x0, hQ_x30, hQ_sp, hQ_cs, hQ_mem⟩
        exact ⟨hQ_pc, hQ_x0, hQ_x30, hQ_sp, hQ_cs, by ecancel⟩
  · obtain ⟨h_x0, h_x30, h_sp, h_cs, h_mem_q⟩ := hst
    kprologue memcpy at "done" with st
    kfinish memcpy
