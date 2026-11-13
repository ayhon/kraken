module

import Kraken.SeparationMem
import Kraken.SeparationTactics
import Kraken.Tactics
import Kraken.X64.Parser
import Kraken.X64.Semantics

/-!
# x86-64 `memcpy` Verification

Functional correctness of System V AMD64 ABI `memcpy(dst, src, n)`.
-/

open Kraken.X64.Parser
open Std.ExtHashMap

/-- System V AMD64 ABI `memcpy(dst, src, n)`:
- Arguments: `%rdi = dst`, `%rsi = src`, `%rdx = n`, `(%rsp) = ra`
- Returns: `%rax = dst`, `%rsp = rsp₀ + 8`, `pc = ra`, callee-saved registers preserved,
  and `src` bytes copied into `dst`. -/
def memcpy : Program := ⸨prog|
memcpy:
  movq %rdi, %rax
  subq $0, %rdx
  jz done
loop:
  movb (%rsi), %cl
  movb %cl, (%rdi)
  addq $1, %rsi
  addq $1, %rdi
  subq $1, %rdx
  jnz loop
done:
  ret
⸩

theorem memcpy_correct [layout : Host memcpy] (s₀ : MachineData)
    (n : Nat) (ra : UInt64) (dst src : List UInt8) (R : DataMem → Prop) :
    (layout memcpy).Spec s₀
      (pre :=
        s₀.regs.rdx.toNat = n ∧
        dst.length = n ∧
        src.length = n ∧
        (s₀.dmem =⋆ ra @ s₀.regs.rsp ⋆ dst @ s₀.regs.rdi ⋆ src @ s₀.regs.rsi ⋆ R))
      (post := fun st =>
        st.pc = Int64.ofBitVec ra.toBitVec ∧
        st.data.regs.rax = s₀.regs.rdi ∧
        st.data.regs.rsp = s₀.regs.rsp + 8 ∧
        st.data.regs.CalleeSavedEq s₀.regs ∧
        (st.data.dmem =⋆ ra @ s₀.regs.rsp ⋆ src @ s₀.regs.rdi ⋆ src @ s₀.regs.rsi ⋆ R)) := by
  rintro ⟨h_rdx, h_dst_len, h_src_len, h_mem⟩
  kloop at "loop"
    (inv := fun v (dst_ptr, src_ptr, dst_bs, src_bs, frame) st =>
      0 < v ∧
      st.data.regs.rdx.toNat = v ∧
      st.data.regs.rdi.toBitVec = dst_ptr ∧
      st.data.regs.rsi.toBitVec = src_ptr ∧
      st.data.regs.rax = s₀.regs.rdi ∧
      st.data.regs.rsp = s₀.regs.rsp ∧
      st.data.regs.CalleeSavedEq s₀.regs ∧
      dst_bs.length = v ∧
      src_bs.length = v ∧
      (st.data.dmem =⋆ dst_bs @ dst_ptr ⋆ src_bs @ src_ptr ⋆ frame))
    (exit := fun _ (dst_ptr, src_ptr, _, src_bs, frame) st =>
      st.pc = (layout memcpy).label "done" ∧
      st.data.regs.rax = s₀.regs.rdi ∧
      st.data.regs.rsp = s₀.regs.rsp ∧
      st.data.regs.CalleeSavedEq s₀.regs ∧
      (st.data.dmem =⋆ src_bs @ dst_ptr ⋆ src_bs @ src_ptr ⋆ frame))
    (measure := n)
    (ghost := (s₀.regs.rdi.toBitVec, s₀.regs.rsi.toBitVec, dst, src, ra @ s₀.regs.rsp ⋆ R))
    with v ⟨dst_ptr, src_ptr, dst_bs, src_bs, frame⟩
      ⟨hv, h_rdx_v, rfl, rfl, h_rax, h_rsp, h_cs, h_dst_v, h_src_v, h_mem_v⟩
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
      kloop_next (v - 1) (rdi.toBitVec + 1#64, rsi.toBitVec + 1#64, dst_bs.drop 1, src_bs.drop 1,
        (src_bs.take 1) @ rdi ⋆ (src_bs.take 1) @ rsi ⋆ frame)
      · kfinish memcpy
      · rintro t_s ⟨hQ_pc, hQ_rax, hQ_rsp, hQ_cs, hQ_mem⟩
        exact ⟨hQ_pc, hQ_rax, hQ_rsp, hQ_cs, by ecancel⟩
  · obtain ⟨h_rax, h_rsp, h_cs, h_mem_q⟩ := hst
    kprologue memcpy at "done" with st
    kfinish memcpy
