module

import Kraken.AArch64.Parser
import Kraken.AArch64.Semantics
import Kraken.BitVecArith
import Kraken.SeparationMem
import Kraken.SeparationTactics
import Kraken.Tactics
import Kraken.ToBytes

/-!
# AArch64 `memmove` Verification

Functional correctness of AAPCS64 `memmove(dst, src, n)` with arbitrary buffer overlap.
-/

open Kraken.AArch64
open Kraken.AArch64.Parser
open Std.ExtHashMap

/-- AAPCS64 `memmove(dst, src, n)`:
- Arguments: `x0 = dst`, `x1 = src`, `x2 = n`, `x30 (lr) = ra`
- Returns: `x0 = dst`, `sp = sp₀`, `pc = x30₀`, callee-saved registers preserved,
  and `src` bytes copied into `dst` (copying forward if `dst < src`, backward if `dst > src`). -/
def memmove : Program := ⸨prog|
memmove:
  mov x3, x0
  cbz x2, done
  cmp x3, x1
  b.eq done
  b.lo forward_loop
  add x1, x1, x2
  add x3, x3, x2
backward_loop:
  sub x1, x1, #1
  sub x3, x3, #1
  ldrb w4, [x1]
  strb w4, [x3]
  sub x2, x2, #1
  cbnz x2, backward_loop
  b done
forward_loop:
  ldrb w4, [x1]
  strb w4, [x3]
  add x1, x1, #1
  add x3, x3, #1
  sub x2, x2, #1
  cbnz x2, forward_loop
done:
  ret
⸩

private theorem memmove_forward_loop_spec [layout : Host memmove] (s₀ : MachineData)
    (n d : Nat) (pre src : List UInt8) (R : DataMem → Prop) :
    (layout memmove).Spec s₀
      (pc := (layout memmove).label "forward_loop")
      (pre :=
        0 < n ∧
        0 < d ∧
        s₀.regs.X2.toNat = n ∧
        s₀.regs.X1.toBitVec = s₀.regs.X3.toBitVec + BitVec.ofNat 64 d ∧
        pre.length = d ∧
        src.length = n ∧
        d + n ≤ 2 ^ 64 ∧
        (s₀.dmem =⋆ pre @ s₀.regs.X3 ⋆ src @ s₀.regs.X1 ⋆ R))
      (post := fun st =>
        st.pc = (layout memmove).label "done" ∧
        st.data.regs.X0 = s₀.regs.X0 ∧
        st.data.regs.X30 = s₀.regs.X30 ∧
        st.data.regs.SP = s₀.regs.SP ∧
        st.data.regs.CalleeSavedEq s₀.regs ∧
        (st.data.dmem =⋆
          src @ s₀.regs.X3 ⋆
          ((pre ++ src).drop n) @ (s₀.regs.X3.toBitVec + BitVec.ofNat 64 n) ⋆ R)) := by
  induction n generalizing s₀ pre src R with
  | zero => rintro ⟨hn, _⟩; omega
  | succ n ih =>
    rintro ⟨_, hd, h_x2, h_x1, h_pre_len, h_src_len, h_bound, h_mem⟩
    kprologue memmove at "forward_loop" to "done" with s₀
    by_cases hn : n = 0
    · subst hn
      kstep
      apply Eventually.done
      refine ⟨by kaddr memmove, rfl, rfl, rfl, Reg64s.CalleeSavedEq_refl _, ?_⟩
      rw [List.drop_append_of_le_length (by omega),
          Mem.At_append_sep (pre.drop 1) src _ (by simp; omega)]
      ecancel
    · kcall ih _ (pre.drop 1 ++ src.take 1) (src.drop 1) ((src.take 1) @ X3 ⋆ R)
        with s₁ ⟨h_x0₁, h_x30₁, h_sp₁, h_cs₁, h_mem₁⟩
      · apply Eventually.done
        refine ⟨rfl, h_x0₁, h_x30₁, h_sp₁, h_cs₁, ?_⟩
        rw [List.append_assoc, List.take_append_drop, ← List.drop_append_of_le_length (by omega),
            List.drop_drop, Nat.add_comm] at h_mem₁
        ecancel
      · refine ⟨by omega, hd, by grind, by grind, by simp [h_pre_len, h_src_len]; omega,
          by simp [h_src_len], by omega, ?_⟩
        rw [Mem.At_append_sep (pre.drop 1) (src.take 1) _ (by simp; omega)]
        ecancel

private theorem memmove_backward_loop_spec [layout : Host memmove] (s₀ : MachineData)
    (n d : Nat) (src_ptr dst_ptr : BitVec 64) (src post : List UInt8) (R : DataMem → Prop) :
    (layout memmove).Spec s₀
      (pc := (layout memmove).label "backward_loop")
      (pre :=
        0 < n ∧
        0 < d ∧
        s₀.regs.X2.toNat = n ∧
        s₀.regs.X1.toBitVec = src_ptr + BitVec.ofNat 64 n ∧
        s₀.regs.X3.toBitVec = dst_ptr + BitVec.ofNat 64 n ∧
        dst_ptr = src_ptr + BitVec.ofNat 64 d ∧
        src.length = n ∧
        post.length = d ∧
        d + n ≤ 2 ^ 64 ∧
        (s₀.dmem =⋆ src @ src_ptr ⋆ post @ (src_ptr + BitVec.ofNat 64 n) ⋆ R))
      (post := fun st =>
        st.pc = (layout memmove).label "done" ∧
        st.data.regs.X0 = s₀.regs.X0 ∧
        st.data.regs.X30 = s₀.regs.X30 ∧
        st.data.regs.SP = s₀.regs.SP ∧
        st.data.regs.CalleeSavedEq s₀.regs ∧
        (st.data.dmem =⋆
          ((src ++ post).take d) @ src_ptr ⋆
          src @ dst_ptr ⋆ R)) := by
  induction n generalizing s₀ src post R with
  | zero => rintro ⟨hn, _⟩; omega
  | succ n ih =>
    rintro ⟨_, hd, h_x2, h_x1, h_x3, h_dst_ptr, h_src_len, h_post_len, h_bound, h_mem⟩
    kprologue memmove at "backward_loop" to "forward_loop" with s₀
    by_cases hn : n = 0
    · subst hn
      rw [Mem.At_take_drop_sep post (d - 1) (src_ptr + 1#64) (by omega) (by omega)] at h_mem
      kstep
      apply Eventually.done
      refine ⟨by kaddr memmove, rfl, rfl, rfl, Reg64s.CalleeSavedEq_refl _, ?_⟩
      rw [List.take_append, h_src_len, List.take_of_length_le (by omega),
          Mem.At_append_sep src (post.take (d - 1)) _ (by simp; omega)]
      ecancel
    · rw [Mem.At_take_drop_sep src n src_ptr (by omega) (by omega),
          Mem.At_take_drop_sep post (d - 1) (src_ptr + BitVec.ofNat 64 (n + 1)) (by omega) (by omega)] at h_mem
      kcall ih _ (src.take n) (src.drop n ++ post.take (d - 1))
        ((src.drop n) @ (dst_ptr + BitVec.ofNat 64 n) ⋆ R)
        with s₁ ⟨h_x0₁, h_x30₁, h_sp₁, h_cs₁, h_mem₁⟩
      · apply Eventually.done
        refine ⟨rfl, h_x0₁, h_x30₁, h_sp₁, h_cs₁, ?_⟩
        rw [← List.append_assoc, List.take_append_drop, List.take_append, List.take_take,
            Nat.min_eq_left (by omega), ← List.take_append] at h_mem₁
        ecancel
      · refine ⟨by omega, hd, by grind, by grind, by grind, h_dst_ptr,
          by simp [h_src_len], by simp [h_src_len, h_post_len]; omega, by omega, ?_⟩
        rw [Mem.At_append_sep (src.drop n) (post.take (d - 1)) _ (by simp; omega)]
        ecancel

theorem memmove_correct [layout : Host memmove] (s₀ : MachineData)
    (base : UInt64) (dst_off src_off n : Nat) (buf : List UInt8) (R : DataMem → Prop) :
    (layout memmove).Spec s₀
      (pre :=
        s₀.regs.X0.toNat = base.toNat + dst_off ∧
        s₀.regs.X1.toNat = base.toNat + src_off ∧
        s₀.regs.X2.toNat = n ∧
        dst_off + n ≤ buf.length ∧
        src_off + n ≤ buf.length ∧
        base.toNat + buf.length ≤ 2 ^ 64 ∧
        (s₀.dmem =⋆ buf @ base ⋆ R))
      (post := fun st =>
        st.pc = Int64.ofBitVec s₀.regs.X30.toBitVec ∧
        st.data.regs.X0 = s₀.regs.X0 ∧
        st.data.regs.SP = s₀.regs.SP ∧
        st.data.regs.CalleeSavedEq s₀.regs ∧
        (st.data.dmem =⋆ (memmoveBytes buf dst_off src_off n) @ base ⋆ R)) := by
  rintro ⟨h_x0, h_x1, h_x2, h_dst_bound, h_src_bound, h_bound, h_mem⟩
  refine Eventually.bind
    (p := fun st =>
      st.pc = (layout memmove).label "done" ∧
      st.data.regs.X0 = s₀.regs.X0 ∧
      st.data.regs.X30 = s₀.regs.X30 ∧
      st.data.regs.SP = s₀.regs.SP ∧
      st.data.regs.CalleeSavedEq s₀.regs ∧
      (st.data.dmem =⋆ (memmoveBytes buf dst_off src_off n) @ base ⋆ R))
    ?_ ?_
  · kprologue memmove to "backward_loop" with s₀
    by_cases hn : n = 0
    · subst hn
      kstep
      apply Eventually.done
      refine ⟨by kaddr memmove, rfl, rfl, rfl, Reg64s.CalleeSavedEq_refl _, ?_⟩
      simp only [memmoveBytes, List.take_zero, List.append_nil, Nat.add_zero, List.take_append_drop]
      ecancel
    · by_cases h_eq : dst_off = src_off
      · subst h_eq
        kstep
        apply Eventually.done
        refine ⟨by kaddr memmove, rfl, rfl, rfl, Reg64s.CalleeSavedEq_refl _, ?_⟩
        rw [memmoveBytes, List.append_assoc, ← List.drop_drop, List.take_append_drop,
            List.take_append_drop]
        ecancel
      · by_cases h_lt : dst_off < src_off
        · obtain ⟨d, rfl⟩ : ∃ d, src_off = dst_off + d := ⟨src_off - dst_off, by omega⟩
          kstep
          rw [Mem.At_take_drop_sep buf dst_off _ (by omega) (by omega),
              Mem.At_take_drop_sep (buf.drop dst_off) d _ (by simp; omega) (by simp; omega),
              List.drop_drop,
              Mem.At_take_drop_sep (buf.drop (dst_off + d)) n _ (by simp; omega) (by simp; omega),
              List.drop_drop] at h_mem
          kcall memmove_forward_loop_spec _ n d
            ((buf.drop dst_off).take d) ((buf.drop (dst_off + d)).take n)
            ((buf.take dst_off) @ base ⋆
              (buf.drop (dst_off + d + n)) @
                (base.toBitVec + BitVec.ofNat 64 dst_off + BitVec.ofNat 64 d + BitVec.ofNat 64 n) ⋆ R)
            ⟨by omega, by omega, by grind, by grind, by simp; omega, by simp; omega, by omega,
             by ecancel⟩
            with s₁ ⟨h_x0₁, h_x30₁, h_sp₁, h_cs₁, h_mem₁⟩
          apply Eventually.done
          refine ⟨rfl, h_x0₁, h_x30₁, h_sp₁, h_cs₁, ?_⟩
          rw [memmoveBytes, List.append_assoc,
              Mem.At_append_sep (buf.take dst_off) _ _ (by simp; omega),
              Mem.At_append_sep ((buf.drop (dst_off + d)).take n) _ _ (by simp; omega),
              ← memmove_forward_drop_eq buf dst_off d n h_src_bound,
              Mem.At_append_sep _ (buf.drop (dst_off + d + n)) _ (by simp; omega),
              show (((buf.drop dst_off).take d ++ (buf.drop (dst_off + d)).take n).drop n).length = d
                by simp; omega]
          ecancel
        · obtain ⟨d, rfl⟩ : ∃ d, dst_off = src_off + d := ⟨dst_off - src_off, by omega⟩
          kstep
          rw [Mem.At_take_drop_sep buf src_off _ (by omega) (by omega),
              Mem.At_take_drop_sep (buf.drop src_off) n _ (by simp; omega) (by simp; omega),
              List.drop_drop,
              Mem.At_take_drop_sep (buf.drop (src_off + n)) d _ (by simp; omega) (by simp; omega),
              List.drop_drop, show src_off + n + d = src_off + d + n by omega] at h_mem
          kcall memmove_backward_loop_spec _ n d X1.toBitVec X0.toBitVec
            ((buf.drop src_off).take n) ((buf.drop (src_off + n)).take d)
            ((buf.take src_off) @ base ⋆
              (buf.drop (src_off + d + n)) @ (base.toBitVec + BitVec.ofNat 64 (src_off + d + n)) ⋆ R)
            ⟨by omega, by omega, by grind, by grind, by grind, by grind,
             by simp; omega, by simp; omega, by omega, by ecancel⟩
            with s₁ ⟨h_x0₁, h_x30₁, h_sp₁, h_cs₁, h_mem₁⟩
          apply Eventually.done
          refine ⟨rfl, h_x0₁, h_x30₁, h_sp₁, h_cs₁, ?_⟩
          rw [memmoveBytes, List.append_assoc,
              Mem.At_append_sep (buf.take (src_off + d)) _ _ (by simp; omega),
              Mem.At_append_sep ((buf.drop src_off).take n) _ _ (by simp; omega),
              ← memmove_backward_take_eq buf src_off d n,
              Mem.At_append_sep (buf.take src_off) _ _ (by simp; omega)]
          ecancel
  · rintro ⟨st, pc⟩ ⟨rfl, h_x0, h_x30, h_sp, h_cs, h_mem_done⟩
    kprologue memmove at "done" with st
    kfinish memmove
