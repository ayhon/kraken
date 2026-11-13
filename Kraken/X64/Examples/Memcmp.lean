module

import Kraken.SeparationMem
import Kraken.SeparationTactics
import Kraken.Tactics
import Kraken.ToBytes
import Kraken.X64.Parser
import Kraken.X64.Semantics

/-!
# x86-64 Constant-Time `memcmp` Verification

Functional correctness and constant-time security of System V AMD64 ABI `memcmp(a, b, n)`:
1. Functional correctness: `%rax` holds `diffAcc a b` (the bitwise OR of `(a[i] ^^^ b[i])`),
   which is `0` iff `a = b`.
2. Constant-time security: for fixed public pointers `p_a`, `p_b`, stack pointer `p_sp`, and
   length `n`, there exists a single leakage trace `tr` produced for all secret byte slices `a`, `b`.
-/

open Kraken.X64.Parser
open Std.ExtHashMap

/-- Constant-time System V AMD64 ABI `memcmp(a, b, n)`:
- Arguments: `%rdi = a`, `%rsi = b`, `%rdx = n`, `(%rsp) = ra`
- Returns: `%rax = diffAcc a b` (`0` iff `a = b`), with no early exit on mismatch. -/
def memcmp : Program := ⸨prog|
memcmp:
  movq $0, %rax
  subq $0, %rdx
  jz done
loop:
  movzbq (%rdi), %rcx
  movzbq (%rsi), %r8
  xorq %r8, %rcx
  orq %rcx, %rax
  addq $1, %rdi
  addq $1, %rsi
  subq $1, %rdx
  jnz loop
done:
  ret
⸩

block_spec memcmp_ct_correct memcmp (p_a p_b p_sp : BitVec 64) (n : Nat)
    s₀ (ra : UInt64) (a b : List UInt8) (R : DataMem → Prop) ct
  (pre :=
    s₀.regs.rdi.toBitVec = p_a ∧
    s₀.regs.rsi.toBitVec = p_b ∧
    s₀.regs.rsp.toBitVec = p_sp ∧
    s₀.regs.rdx.toNat = n ∧
    a.length = n ∧
    b.length = n ∧
    (s₀.dmem =⋆ ra @ s₀.regs.rsp ⋆ a @ p_a ⋆ b @ p_b ⋆ R))
  (post := fun st =>
    st.pc = Int64.ofBitVec ra.toBitVec ∧
    st.data.regs.rax.toBitVec = diffAcc a b ∧
    (st.data.regs.rax = 0 ↔ a = b) ∧
    st.data.regs.rsp = s₀.regs.rsp + 8 ∧
    st.data.regs.CalleeSavedEq s₀.regs ∧
    (st.data.dmem =⋆ ra @ s₀.regs.rsp ⋆ a @ p_a ⋆ b @ p_b ⋆ R)) := by
  kloop at "loop"
    (pubinv := fun v _ => 0 < v)
    (inv := fun v (a_ptr, b_ptr) s₀ (ra, _, _, _) (a_bs, b_bs, acc, frame) st =>
      st.data.regs.rdx.toNat = v ∧
      st.data.regs.rdi.toBitVec = a_ptr ∧
      st.data.regs.rsi.toBitVec = b_ptr ∧
      st.data.regs.rax.toBitVec = acc ∧
      st.data.regs.rsp = s₀.regs.rsp ∧
      st.data.regs.rsp.toBitVec = p_sp ∧
      st.data.regs.CalleeSavedEq s₀.regs ∧
      a_bs.length = v ∧
      b_bs.length = v ∧
      (st.data.dmem =⋆ ra @ p_sp ⋆ a_bs @ a_ptr ⋆ b_bs @ b_ptr ⋆ frame))
    (exit := fun _ (a_ptr, b_ptr) s₀ (ra, _, _, _) (a_bs, b_bs, acc, frame) st =>
      st.pc = (layout memcmp).label "done" ∧
      st.data.regs.rax.toBitVec = acc ||| diffAcc a_bs b_bs ∧
      st.data.regs.rsp = s₀.regs.rsp ∧
      st.data.regs.rsp.toBitVec = p_sp ∧
      st.data.regs.CalleeSavedEq s₀.regs ∧
      a_bs.length = b_bs.length ∧
      (st.data.dmem =⋆ ra @ p_sp ⋆ a_bs @ a_ptr ⋆ b_bs @ b_ptr ⋆ frame))
    (measure := n)
    (pub := (p_a, p_b))
    (ghost := fun _ (_, a, b, R) => (a, b, 0#64, R))
    with v ⟨a_ptr, b_ptr⟩ hv
  · by_cases hn : n = 0
    · subst hn
      kloop_exit
      kintro s ⟨ra, a, b, R⟩ ⟨h_rdi, h_rsi, h_rsp, h_rdx, h_a_len, h_b_len, h_mem⟩
      rw [h_rsp] at h_mem
      kprologue memcmp to "loop" with s
      obtain rfl := List.eq_nil_of_length_eq_zero h_a_len
      obtain rfl := List.eq_nil_of_length_eq_zero h_b_len
      kfinish memcmp
    · kloop_next
      refine ⟨by omega, ?_⟩
      kintro s ⟨ra, a, b, R⟩ ⟨h_rdi, h_rsi, h_rsp, h_rdx, h_a_len, h_b_len, h_mem⟩
      rw [h_rsp] at h_mem
      kprologue memcmp to "loop" with s
      kfinish memcmp
  · by_cases hv1 : v = 1
    · subst hv1
      kloop_exit
      kintro s₀ ⟨ra, a, b, R⟩ ⟨a_bs, b_bs, acc, frame⟩ ⟨s, pc⟩
        ⟨rfl, h_rdx_v, h_rdi_v, h_rsi_v, h_rax_v, h_rsp, h_rsp_p, h_cs, h_a_v, h_b_v, h_mem_v⟩
      kprologue memcmp at "loop" to "done" with s
      have := diffAcc_one a_bs b_bs h_a_v h_b_v acc
      kfinish memcmp
    · kloop_next (v - 1) (a_ptr + 1#64, b_ptr + 1#64)
      kintro s₀ ⟨ra, a, b, R⟩ ⟨a_bs, b_bs, acc, frame⟩ ⟨s, pc⟩
        ⟨rfl, h_rdx_v, h_rdi_v, h_rsi_v, h_rax_v, h_rsp, h_rsp_p, h_cs, h_a_v, h_b_v, h_mem_v⟩
      kprologue memcmp at "loop" to "done" with s
      kstep
      kdone
      refine ⟨(a_bs.drop 1, b_bs.drop 1,
        acc ||| ((BitVec.ofInt 8 (Int.ofBytes (a_bs.take 1))).setWidth 64 ^^^
                 (BitVec.ofInt 8 (Int.ofBytes (b_bs.take 1))).setWidth 64),
        (a_bs.take 1) @ a_ptr ⋆ (b_bs.take 1) @ b_ptr ⋆ frame),
        ⟨by kaddr memcmp, by grind, by grind, by grind, by grind,
         h_rsp, h_rsp_p, h_cs, by simp [h_a_v], by simp [h_b_v], by ecancel⟩,
        ?_⟩
      rintro t_s ⟨hQ_pc, hQ_rax, hQ_rsp, hQ_rsp_p, hQ_cs, _, hQ_mem⟩
      refine ⟨hQ_pc, ?_, hQ_rsp, hQ_rsp_p, hQ_cs, by omega, by ecancel⟩
      rw [hQ_rax]
      exact diffAcc_step a_bs b_bs (by omega) (by omega) acc
  · kintro s₀ ⟨ra, a, b, R⟩ ⟨st, pc⟩ ⟨rfl, h_rax, h_rsp, h_rsp_p, h_cs, h_ab_len, h_mem_q⟩
    have h_rsp0 : s₀.regs.rsp.toBitVec = p_sp := by rw [← h_rsp, h_rsp_p]
    kprologue memcmp at "done" with st
    have h_diff := diffAcc_eq_zero_iff a b h_ab_len
    kfinish memcmp
