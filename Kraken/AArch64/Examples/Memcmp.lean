module

import Kraken.AArch64.Parser
import Kraken.AArch64.Semantics
import Kraken.SeparationMem
import Kraken.SeparationTactics
import Kraken.Tactics
import Kraken.ToBytes

/-!
# AArch64 Constant-Time `memcmp` Verification

Functional correctness and constant-time security of AAPCS64 `memcmp(a, b, n)`:
1. Functional correctness: `x0` holds `diffAcc a b` (the bitwise OR of `(a[i] ^^^ b[i])`),
   which is `0` iff `a = b`.
2. Constant-time security: for fixed public pointers `p_a`, `p_b` and length `n`,
   there exists a single leakage trace `tr` produced for all secret byte slices `a`, `b`.
-/

open Kraken.AArch64
open Kraken.AArch64.Parser
open Std.ExtHashMap

/-- Constant-time AAPCS64 `memcmp(a, b, n)`:
- Arguments: `x0 = a`, `x1 = b`, `x2 = n`, `x30 (lr) = ra`
- Returns: `x0 = diffAcc a b` (`0` iff `a = b`), `sp = sp₀`, `pc = x30₀`,
  callee-saved registers and memory preserved, with no early exit on mismatch. -/
def memcmp : Program := ⸨prog|
memcmp:
  mov x3, #0
  cbz x2, done
loop:
  ldrb w4, [x0]
  ldrb w5, [x1]
  eor w4, w4, w5
  orr x3, x3, x4
  add x0, x0, #1
  add x1, x1, #1
  sub x2, x2, #1
  cbnz x2, loop
done:
  mov x0, x3
  ret
⸩

block_spec memcmp_ct_correct memcmp (p_a p_b : BitVec 64) (n : Nat)
    s₀ (a b : List UInt8) (R : DataMem → Prop) ct
  (pre :=
    s₀.regs.X0.toBitVec = p_a ∧
    s₀.regs.X1.toBitVec = p_b ∧
    s₀.regs.X2.toNat = n ∧
    a.length = n ∧
    b.length = n ∧
    (s₀.dmem =⋆ a @ p_a ⋆ b @ p_b ⋆ R))
  (post := fun st =>
    st.pc = Int64.ofBitVec s₀.regs.X30.toBitVec ∧
    st.data.regs.X0.toBitVec = diffAcc a b ∧
    (st.data.regs.X0 = 0 ↔ a = b) ∧
    st.data.regs.SP = s₀.regs.SP ∧
    st.data.regs.CalleeSavedEq s₀.regs ∧
    (st.data.dmem =⋆ a @ p_a ⋆ b @ p_b ⋆ R)) := by
  kloop at "loop"
    (pubinv := fun v _ => 0 < v)
    (inv := fun v (a_ptr, b_ptr) s₀ _ (a_bs, b_bs, acc, frame) st =>
      st.data.regs.X2.toNat = v ∧
      st.data.regs.X0.toBitVec = a_ptr ∧
      st.data.regs.X1.toBitVec = b_ptr ∧
      st.data.regs.X3.toBitVec = acc ∧
      st.data.regs.X30 = s₀.regs.X30 ∧
      st.data.regs.SP = s₀.regs.SP ∧
      st.data.regs.CalleeSavedEq s₀.regs ∧
      a_bs.length = v ∧
      b_bs.length = v ∧
      (st.data.dmem =⋆ a_bs @ a_ptr ⋆ b_bs @ b_ptr ⋆ frame))
    (exit := fun _ (a_ptr, b_ptr) s₀ _ (a_bs, b_bs, acc, frame) st =>
      st.pc = (layout memcmp).label "done" ∧
      st.data.regs.X3.toBitVec = acc ||| diffAcc a_bs b_bs ∧
      st.data.regs.X30 = s₀.regs.X30 ∧
      st.data.regs.SP = s₀.regs.SP ∧
      st.data.regs.CalleeSavedEq s₀.regs ∧
      a_bs.length = b_bs.length ∧
      (st.data.dmem =⋆ a_bs @ a_ptr ⋆ b_bs @ b_ptr ⋆ frame))
    (measure := n)
    (pub := (p_a, p_b))
    (ghost := fun _ (a, b, R) => (a, b, 0#64, R))
    with v ⟨a_ptr, b_ptr⟩ hv
  · by_cases hn : n = 0
    · subst hn
      kloop_exit
      kintro s ⟨a, b, R⟩ ⟨h_x0, h_x1, h_x2, h_a_len, h_b_len, h_mem⟩
      kprologue memcmp to "loop" with s
      obtain rfl := List.eq_nil_of_length_eq_zero h_a_len
      obtain rfl := List.eq_nil_of_length_eq_zero h_b_len
      kfinish memcmp
    · kloop_next
      refine ⟨by omega, ?_⟩
      kintro s ⟨a, b, R⟩ ⟨h_x0, h_x1, h_x2, h_a_len, h_b_len, h_mem⟩
      kprologue memcmp to "loop" with s
      kfinish memcmp
  · by_cases hv1 : v = 1
    · subst hv1
      kloop_exit
      kintro s₀ ⟨a, b, R⟩ ⟨a_bs, b_bs, acc, frame⟩ ⟨s, pc⟩
        ⟨rfl, h_x2_v, h_x0_v, h_x1_v, h_x3_v, h_x30, h_sp, h_cs, h_a_v, h_b_v, h_mem_v⟩
      kprologue memcmp at "loop" to "done" with s
      have := diffAcc_one_32 a_bs b_bs h_a_v h_b_v acc
      kfinish memcmp
    · kloop_next (v - 1) (a_ptr + 1#64, b_ptr + 1#64)
      kintro s₀ ⟨a, b, R⟩ ⟨a_bs, b_bs, acc, frame⟩ ⟨s, pc⟩
        ⟨rfl, h_x2_v, h_x0_v, h_x1_v, h_x3_v, h_x30, h_sp, h_cs, h_a_v, h_b_v, h_mem_v⟩
      kprologue memcmp at "loop" to "done" with s
      kstep
      kdone
      refine ⟨(a_bs.drop 1, b_bs.drop 1,
        acc ||| (((BitVec.ofInt 8 (Int.ofBytes (a_bs.take 1))).setWidth 32 ^^^
                  (BitVec.ofInt 8 (Int.ofBytes (b_bs.take 1))).setWidth 32).setWidth 64),
        (a_bs.take 1) @ a_ptr ⋆ (b_bs.take 1) @ b_ptr ⋆ frame),
        ⟨by kaddr memcmp, by grind, by grind, by grind, by grind,
         h_x30, h_sp, h_cs, by simp [h_a_v], by simp [h_b_v], by ecancel⟩,
        ?_⟩
      rintro t_s ⟨hQ_pc, hQ_x3, hQ_x30, hQ_sp, hQ_cs, _, hQ_mem⟩
      refine ⟨hQ_pc, ?_, hQ_x30, hQ_sp, hQ_cs, by omega, by ecancel⟩
      rw [hQ_x3]
      exact diffAcc_step_32 a_bs b_bs (by omega) (by omega) acc
  · kintro s₀ ⟨a, b, R⟩ ⟨st, pc⟩ ⟨rfl, h_x3, h_x30, h_sp, h_cs, h_ab_len, h_mem_q⟩
    kprologue memcmp at "done" with st
    have h_diff := diffAcc_eq_zero_iff a b h_ab_len
    kfinish memcmp
