module

import Kraken.AArch64.Parser
import Kraken.AArch64.Semantics
import Kraken.BitVecArith
import Kraken.SeparationMem
import Kraken.SeparationTactics
import Kraken.Tactics
import Kraken.ToBytes

/-!
# Verification of BoringSSL's `bn_add_words` and `bn_sub_words`

Functional correctness of `bn_add_words` and `bn_sub_words` from BoringSSL's
`third_party/openssl/boringssl/src/gen/bcm/bn-armv8-linux.S` (stripped of assembler directives
and `AARCH64_VALID_CALL_TARGET` BTI macro annotations).
-/

open Kraken.AArch64
open Kraken.AArch64.Parser
open Std.ExtHashMap

def bn_add_words : Program := ⸨prog|
-- BN_ULONG bn_add_words(BN_ULONG *rp, const BN_ULONG *ap, const BN_ULONG *bp,
--                       size_t num);
bn_add_words:
  -- Clear the carry flag.
  cmn xzr, xzr

  -- aarch64 can load two registers at a time, so we do two loop iterations at
  -- at a time. Split x3 = 2 * x8 + x3. This allows loop
  -- operations to use CBNZ without clobbering the carry flag.
  lsr x8, x3, #1
  and x3, x3, #1

  cbz x8, .Ladd_tail
.Ladd_loop:
  ldp x4, x5, [x1], #16
  ldp x6, x7, [x2], #16
  sub x8, x8, #1
  adcs x4, x4, x6
  adcs x5, x5, x7
  stp x4, x5, [x0], #16
  cbnz x8, .Ladd_loop

.Ladd_tail:
  cbz x3, .Ladd_exit
  ldr x4, [x1], #8
  ldr x6, [x2], #8
  adcs x4, x4, x6
  str x4, [x0], #8

.Ladd_exit:
  cset x0, cs
  ret
⸩

def bn_sub_words : Program := ⸨prog|
-- BN_ULONG bn_sub_words(BN_ULONG *rp, const BN_ULONG *ap, const BN_ULONG *bp,
--                       size_t num);
bn_sub_words:
  -- Set the carry flag. Arm's borrow bit is flipped from the carry flag,
  -- so we want C = 1 here.
  cmp xzr, xzr

  -- aarch64 can load two registers at a time, so we do two loop iterations at
  -- at a time. Split x3 = 2 * x8 + x3. This allows loop
  -- operations to use CBNZ without clobbering the carry flag.
  lsr x8, x3, #1
  and x3, x3, #1

  cbz x8, .Lsub_tail
.Lsub_loop:
  ldp x4, x5, [x1], #16
  ldp x6, x7, [x2], #16
  sub x8, x8, #1
  sbcs x4, x4, x6
  sbcs x5, x5, x7
  stp x4, x5, [x0], #16
  cbnz x8, .Lsub_loop

.Lsub_tail:
  cbz x3, .Lsub_exit
  ldr x4, [x1], #8
  ldr x6, [x2], #8
  sbcs x4, x4, x6
  str x4, [x0], #8

.Lsub_exit:
  cset x0, cc
  ret
⸩

/-! ## Multi-Limb Carry/Borrow Arithmetic -/

private theorem pow_256_16_mul_pred (v : Nat) (hv : 0 < v) :
    (256 : Int) ^ 16 * 256 ^ (16 * (v - 1)) = 256 ^ (16 * v) := by
  rw [← Int.pow_add, show 16 + 16 * (v - 1) = 16 * v by omega]

/-! ## Verification of `bn_add_words` -/

block_spec bn_add_words_correct bn_add_words s₀
  (num : Nat) (rp ap bp : List UInt8) (R : DataMem → Prop)
  (pre :=
    s₀.regs.X3.toNat = num ∧
    8 * num ≤ 2 ^ 64 ∧
    rp.length = 8 * num ∧
    ap.length = 8 * num ∧
    bp.length = 8 * num ∧
    (s₀.dmem =⋆ rp @ s₀.regs.X0 ⋆ ap @ s₀.regs.X1 ⋆ bp @ s₀.regs.X2 ⋆ R))
  (post := fun st =>
    st.pc = Int64.ofBitVec s₀.regs.X30.toBitVec ∧
    st.data.regs.SP = s₀.regs.SP ∧
    st.data.regs.CalleeSavedEq s₀.regs ∧
    st.data.regs.X0.toNat ≤ 1 ∧
    ∃ out : List UInt8,
      out.length = 8 * num ∧
      Int.ofBytes out + (st.data.regs.X0.toNat : Int) * 256 ^ (8 * num) =
        Int.ofBytes ap + Int.ofBytes bp ∧
      (st.data.dmem =⋆ out @ s₀.regs.X0 ⋆ ap @ s₀.regs.X1 ⋆ bp @ s₀.regs.X2 ⋆ R)) := by
  rintro ⟨h_x3, h_num_bound, h_rp_len, h_ap_len, h_bp_len, h_mem⟩
  kloop at ".Ladd_loop"
    (inv := fun v (rp_ptr, ap_ptr, bp_ptr, rp_bs, ap_bs, bp_bs, c, frame) st =>
      0 < v ∧
      16 * v + 8 * (num % 2) ≤ 2 ^ 64 ∧
      st.data.regs.X8.toNat = v ∧
      st.data.regs.X3.toNat = num % 2 ∧
      st.data.regs.X0.toBitVec = rp_ptr ∧
      st.data.regs.X1.toBitVec = ap_ptr ∧
      st.data.regs.X2.toBitVec = bp_ptr ∧
      st.data.regs.X30 = s₀.regs.X30 ∧
      st.data.regs.SP = s₀.regs.SP ∧
      st.data.regs.CalleeSavedEq s₀.regs ∧
      st.data.status.c = c ∧
      rp_bs.length = 16 * v + 8 * (num % 2) ∧
      ap_bs.length = 16 * v + 8 * (num % 2) ∧
      bp_bs.length = 16 * v + 8 * (num % 2) ∧
      (st.data.dmem =⋆ rp_bs @ rp_ptr ⋆ ap_bs @ ap_ptr ⋆ bp_bs @ bp_ptr ⋆ frame))
    (exit := fun v (rp_ptr, ap_ptr, bp_ptr, rp_bs, ap_bs, bp_bs, c, frame) st =>
      st.pc = (layout bn_add_words).label ".Ladd_tail" ∧
      st.data.regs.X3.toNat = num % 2 ∧
      st.data.regs.X0.toBitVec = rp_ptr + BitVec.ofNat 64 (16 * v) ∧
      st.data.regs.X1.toBitVec = ap_ptr + BitVec.ofNat 64 (16 * v) ∧
      st.data.regs.X2.toBitVec = bp_ptr + BitVec.ofNat 64 (16 * v) ∧
      st.data.regs.X30 = s₀.regs.X30 ∧
      st.data.regs.SP = s₀.regs.SP ∧
      st.data.regs.CalleeSavedEq s₀.regs ∧
      ∃ r_pairs : List UInt8,
        r_pairs.length = 16 * v ∧
        Int.ofBytes r_pairs + (if st.data.status.c then 1 else 0) * 256 ^ (16 * v) =
          Int.ofBytes (ap_bs.take (16 * v)) + Int.ofBytes (bp_bs.take (16 * v)) + (if c then 1 else 0) ∧
        (st.data.dmem =⋆
          r_pairs @ rp_ptr ⋆
          (rp_bs.drop (16 * v)) @ (rp_ptr + BitVec.ofNat 64 (16 * v)) ⋆
          ap_bs @ ap_ptr ⋆ bp_bs @ bp_ptr ⋆ frame))
    (measure := num / 2)
    (ghost := (s₀.regs.X0.toBitVec, s₀.regs.X1.toBitVec, s₀.regs.X2.toBitVec, rp, ap, bp, false, R))
    (state := s)
    with v ⟨rp_ptr, ap_ptr, bp_ptr, rp_bs, ap_bs, bp_bs, c, frame⟩
      ⟨hv, h_v_bound, h_x8, h_x3_mod, rfl, rfl, rfl, h_x30, h_sp, h_cs, rfl, h_rp_v, h_ap_v, h_bp_v, h_mem_v⟩
  · kprologue bn_add_words to ".Ladd_loop" with s₀
    by_cases hn2 : num / 2 = 0
    · have h_shift_zero : (X3.toBitVec >>> 1 = 0#64) :=
        (UInt64.ushiftRight_one_eq_zero_iff X3).mpr (by omega)
      kloop_exit
      refine ⟨by kaddr bn_add_words, by grind, ?_, ?_, ?_, rfl, rfl,
        Reg64s.CalleeSavedEq_refl _, [], by simp [hn2], by simp +zetaDelta [hn2, Int.ofBytes], ?_⟩
      · simp [hn2]
      · simp [hn2]
      · simp [hn2]
      · simp only [hn2, Nat.mul_zero, List.drop_zero, BitVec.add_zero]
        rw [Mem.At_nil_sep]
        ecancel
    · have h_shift_nz : ¬ (X3.toBitVec >>> 1 = 0#64) := by
        rw [UInt64.ushiftRight_one_eq_zero_iff]; omega
      kloop_next
      exact ⟨by omega, by omega, by grind, by grind,
        rfl, rfl, rfl, rfl, rfl, Reg64s.CalleeSavedEq_refl _, rfl,
        by omega, by omega, by omega, by ecancel⟩
  · by_cases hv1 : v = 1
    · subst hv1
      kprologue bn_add_words at ".Ladd_loop" to ".Ladd_tail" with s
      kloop_exit
      refine ⟨by kaddr bn_add_words, h_x3_mod, by grind, by grind, by grind,
        h_x30, h_sp, h_cs, ?_⟩
      have h_step0 := adcs_step_bytes (ap_bs.take 8) (bp_bs.take 8) flags.c
        (by simp; omega) (by simp; omega)
      have h_step1 := adcs_step_bytes ((ap_bs.drop 8).take 8) ((bp_bs.drop 8).take 8)
        (adcsCarry (ap_bs.take 8) (bp_bs.take 8) flags.c)
        (by simp; omega) (by simp; omega)
      let v0 := (adcsWord (ap_bs.take 8) (bp_bs.take 8) flags.c).toInt
      let v1 := (adcsWord ((ap_bs.drop 8).take 8) ((bp_bs.drop 8).take 8)
        (adcsCarry (ap_bs.take 8) (bp_bs.take 8) flags.c)).toInt
      let c1 := adcsCarry ((ap_bs.drop 8).take 8) ((bp_bs.drop 8).take 8)
        (adcsCarry (ap_bs.take 8) (bp_bs.take 8) flags.c)
      refine ⟨Int.toBytes 8 v0 ++ Int.toBytes 8 v1,
        by simp, ?_, by ecancel⟩
      change Int.ofBytes (Int.toBytes 8 v0 ++ Int.toBytes 8 v1) +
        (if c1 then 1 else 0) * 256 ^ (16 * 1) =
        Int.ofBytes (ap_bs.take (16 * 1)) + Int.ofBytes (bp_bs.take (16 * 1)) +
        (if flags.c then 1 else 0)
      rw [Nat.mul_one, Int.ofBytes_append, Int.toBytes_length,
          Int.ofBytes_take_add ap_bs 8 8 (by omega), Int.ofBytes_take_add bp_bs 8 8 (by omega)]
      dsimp +zetaDelta only [v0, v1, c1, adcsCarry, adcsWord] at h_step0 h_step1 ⊢
      omega
    · kprologue bn_add_words at ".Ladd_loop" to ".Ladd_tail" with s
      kstep
      have h_step0 := adcs_step_bytes (ap_bs.take 8) (bp_bs.take 8) flags.c
        (by simp; omega) (by simp; omega)
      have h_step1 := adcs_step_bytes ((ap_bs.drop 8).take 8) ((bp_bs.drop 8).take 8)
        (adcsCarry (ap_bs.take 8) (bp_bs.take 8) flags.c)
        (by simp; omega) (by simp; omega)
      let v0 := (adcsWord (ap_bs.take 8) (bp_bs.take 8) flags.c).toInt
      let v1 := (adcsWord ((ap_bs.drop 8).take 8) ((bp_bs.drop 8).take 8)
        (adcsCarry (ap_bs.take 8) (bp_bs.take 8) flags.c)).toInt
      let c1 := adcsCarry ((ap_bs.drop 8).take 8) ((bp_bs.drop 8).take 8)
        (adcsCarry (ap_bs.take 8) (bp_bs.take 8) flags.c)
      have h_w01_len : (Int.toBytes 8 v0 ++ Int.toBytes 8 v1).length = 16 := by simp
      kloop_next (v - 1)
        (X0.toBitVec + 16#64, X1.toBitVec + 16#64, X2.toBitVec + 16#64,
         rp_bs.drop 16, ap_bs.drop 16, bp_bs.drop 16, c1,
         (Int.toBytes 8 v0 ++ Int.toBytes 8 v1) @ X0 ⋆ (ap_bs.take 16) @ X1 ⋆ (bp_bs.take 16) @ X2 ⋆ frame)
      · exact ⟨by omega, by omega, by grind, h_x3_mod,
          by grind, by grind, by grind, h_x30, h_sp, h_cs, rfl,
          by simp [h_rp_v]; omega, by simp [h_ap_v]; omega, by simp [h_bp_v]; omega,
          by ecancel⟩
      rintro t_s ⟨hQ_pc, hQ_x3, hQ_x0, hQ_x1, hQ_x2, hQ_x30, h_sp, h_cs,
        r_rest, h_r_rest_len, h_r_rest_val, hQ_mem⟩
      have h_16_v : 16 + 16 * (v - 1) = 16 * v := by omega
      have h_16_bound : 16 + 16 * (v - 1) ≤ 2 ^ 64 := by omega
      refine ⟨hQ_pc, hQ_x3, ?_, ?_, ?_, hQ_x30, h_sp, h_cs,
        (Int.toBytes 8 v0 ++ Int.toBytes 8 v1) ++ r_rest, by simp; omega, ?_, ?_⟩
      · rw [hQ_x0, BitVec.add_assoc, ← BitVec.ofNat_add, h_16_v]
      · rw [hQ_x1, BitVec.add_assoc, ← BitVec.ofNat_add, h_16_v]
      · rw [hQ_x2, BitVec.add_assoc, ← BitVec.ofNat_add, h_16_v]
      · rw [Int.ofBytes_append, h_w01_len, ← h_16_v,
            Int.ofBytes_take_add ap_bs 16 (16 * (v - 1)) (by omega),
            Int.ofBytes_take_add bp_bs 16 (16 * (v - 1)) (by omega), h_16_v]
        have h_pair_val : Int.ofBytes (Int.toBytes 8 v0 ++ Int.toBytes 8 v1) =
            Int.ofBytes (ap_bs.take 8) + 256 ^ 8 * Int.ofBytes ((ap_bs.drop 8).take 8) +
            (Int.ofBytes (bp_bs.take 8) + 256 ^ 8 * Int.ofBytes ((bp_bs.drop 8).take 8)) +
            (if flags.c then 1 else 0) -
            (if c1 then 1 else 0) * 256 ^ 16 := by
          rw [Int.ofBytes_append, Int.toBytes_length]
          dsimp +zetaDelta only [v0, v1, c1, adcsCarry, adcsWord] at h_step0 h_step1 ⊢
          omega
        have h_ap16 : Int.ofBytes (ap_bs.take 16) =
            Int.ofBytes (ap_bs.take 8) + 256 ^ 8 * Int.ofBytes ((ap_bs.drop 8).take 8) :=
          Int.ofBytes_take_add ap_bs 8 8 (by omega)
        have h_bp16 : Int.ofBytes (bp_bs.take 16) =
            Int.ofBytes (bp_bs.take 8) + 256 ^ 8 * Int.ofBytes ((bp_bs.drop 8).take 8) :=
          Int.ofBytes_take_add bp_bs 8 8 (by omega)
        have h_pow := pow_256_16_mul_pred v hv
        have h_mul := congrArg ((256 : Int) ^ 16 * ·) h_r_rest_val
        try dsimp only at h_mul
        rw [Int.mul_add, Int.mul_add, Int.mul_left_comm, h_pow] at h_mul
        omega
      · rw [List.drop_drop, show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
            BitVec.add_assoc, ← BitVec.ofNat_add, h_16_v] at hQ_mem
        ecancel
  · obtain ⟨h_x3_mod, h_x0_ptr, h_x1_ptr, h_x2_ptr, h_x30, h_sp, h_cs,
      r_pairs, h_r_pairs_len, h_r_pairs_val, h_mem_q⟩ := hs
    simp only [Bool.false_eq_true, ↓reduceIte, Int.add_zero] at h_r_pairs_val
    by_cases h_odd : num % 2 = 0
    · kprologue bn_add_words at ".Ladd_tail" with s
      have h_x3_zero : X3.toBitVec = 0#64 := by grind
      kstep
      kprologue bn_add_words at ".Ladd_exit"
      kstep
      apply Eventually.done
      have h_16_eq : 16 * (num / 2) = 8 * num := by omega
      have h_ap_take : ap.take (16 * (num / 2)) = ap := List.take_of_length_le (by omega)
      have h_bp_take : bp.take (16 * (num / 2)) = bp := List.take_of_length_le (by omega)
      have h_rp_drop : rp.drop (16 * (num / 2)) = [] := List.drop_eq_nil_of_le (by omega)
      rw [h_rp_drop, Mem.At_nil_sep] at h_mem_q
      refine ⟨by grind, h_sp, h_cs, UInt64.toNat_cset_le_one _,
        r_pairs, by omega, ?_, by ecancel⟩
      change Int.ofBytes r_pairs +
        ((UInt64.ofBitVec (if !flags.c then 0#64 else 1#64) : UInt64).toNat : Int) * 256 ^ (8 * num) =
        Int.ofBytes ap + Int.ofBytes bp
      rw [UInt64.toNat_cset_cs]
      rw [h_ap_take, h_bp_take, h_16_eq] at h_r_pairs_val
      omega
    · rw [Mem.At_take_drop_sep ap (16 * (num / 2)) _ (by omega) (by omega),
          Mem.At_take_drop_sep bp (16 * (num / 2)) _ (by omega) (by omega)] at h_mem_q
      kprologue bn_add_words at ".Ladd_tail" with s
      rw [← h_x0_ptr, ← h_x1_ptr, ← h_x2_ptr] at h_mem_q
      have h_x3_nz : ¬ (X3.toBitVec = 0#64) := by grind
      kstep
      apply Eventually.done
      have h_step_tail := adcs_step_bytes
        (ap.drop (16 * (num / 2)))
        (bp.drop (16 * (num / 2)))
        flags.c
        (by simp; omega) (by simp; omega)
      let v_tail := (adcsWord
        (ap.drop (16 * (num / 2)))
        (bp.drop (16 * (num / 2)))
        flags.c).toInt
      let c_tail := adcsCarry
        (ap.drop (16 * (num / 2)))
        (bp.drop (16 * (num / 2)))
        flags.c
      refine ⟨by grind, h_sp, h_cs, UInt64.toNat_cset_le_one _,
        r_pairs ++ Int.toBytes 8 v_tail, by simp; omega, ?_, ?_⟩
      · change Int.ofBytes (r_pairs ++ Int.toBytes 8 v_tail) +
          ((UInt64.ofBitVec (if !c_tail then 0#64 else 1#64) : UInt64).toNat : Int) * 256 ^ (8 * num) =
          Int.ofBytes ap + Int.ofBytes bp
        rw [UInt64.toNat_cset_cs, Int.ofBytes_append, h_r_pairs_len]
        have h_ap_split := Int.ofBytes_take_drop_pair ap (16 * (num / 2)) (by omega)
        have h_bp_split := Int.ofBytes_take_drop_pair bp (16 * (num / 2)) (by omega)
        have h_pow : (256 : Int) ^ (8 * num) = 256 ^ (16 * (num / 2)) * 256 ^ 8 := by
          rw [← Int.pow_add, show 16 * (num / 2) + 8 = 8 * num by omega]
        have h_mul := congrArg ((256 : Int) ^ (16 * (num / 2)) * ·) h_step_tail
        dsimp +zetaDelta only [v_tail, c_tail, adcsCarry, adcsWord] at h_mul ⊢
        rw [Int.mul_add, Int.mul_add, Int.mul_add, Int.mul_left_comm, ← h_pow] at h_mul
        rw [Int.mul_comm _ (256 ^ (16 * (num / 2)))] at h_r_pairs_val
        omega
      · rw [Mem.At_take_drop_sep ap (16 * (num / 2)) _ (by omega) (by omega),
            Mem.At_take_drop_sep bp (16 * (num / 2)) _ (by omega) (by omega)]
        simp only [h_x0_ptr, h_x1_ptr, h_x2_ptr] at *
        ecancel

/-! ## Verification of `bn_sub_words` -/

block_spec bn_sub_words_correct bn_sub_words s₀
  (num : Nat) (rp ap bp : List UInt8) (R : DataMem → Prop)
  (pre :=
    s₀.regs.X3.toNat = num ∧
    8 * num ≤ 2 ^ 64 ∧
    rp.length = 8 * num ∧
    ap.length = 8 * num ∧
    bp.length = 8 * num ∧
    (s₀.dmem =⋆ rp @ s₀.regs.X0 ⋆ ap @ s₀.regs.X1 ⋆ bp @ s₀.regs.X2 ⋆ R))
  (post := fun st =>
    st.pc = Int64.ofBitVec s₀.regs.X30.toBitVec ∧
    st.data.regs.SP = s₀.regs.SP ∧
    st.data.regs.CalleeSavedEq s₀.regs ∧
    st.data.regs.X0.toNat ≤ 1 ∧
    ∃ out : List UInt8,
      out.length = 8 * num ∧
      Int.ofBytes out - (st.data.regs.X0.toNat : Int) * 256 ^ (8 * num) =
        Int.ofBytes ap - Int.ofBytes bp ∧
      (st.data.dmem =⋆ out @ s₀.regs.X0 ⋆ ap @ s₀.regs.X1 ⋆ bp @ s₀.regs.X2 ⋆ R)) := by
  rintro ⟨h_x3, h_num_bound, h_rp_len, h_ap_len, h_bp_len, h_mem⟩
  kloop at ".Lsub_loop"
    (inv := fun v (rp_ptr, ap_ptr, bp_ptr, rp_bs, ap_bs, bp_bs, c, frame) st =>
      0 < v ∧
      16 * v + 8 * (num % 2) ≤ 2 ^ 64 ∧
      st.data.regs.X8.toNat = v ∧
      st.data.regs.X3.toNat = num % 2 ∧
      st.data.regs.X0.toBitVec = rp_ptr ∧
      st.data.regs.X1.toBitVec = ap_ptr ∧
      st.data.regs.X2.toBitVec = bp_ptr ∧
      st.data.regs.X30 = s₀.regs.X30 ∧
      st.data.regs.SP = s₀.regs.SP ∧
      st.data.regs.CalleeSavedEq s₀.regs ∧
      st.data.status.c = c ∧
      rp_bs.length = 16 * v + 8 * (num % 2) ∧
      ap_bs.length = 16 * v + 8 * (num % 2) ∧
      bp_bs.length = 16 * v + 8 * (num % 2) ∧
      (st.data.dmem =⋆ rp_bs @ rp_ptr ⋆ ap_bs @ ap_ptr ⋆ bp_bs @ bp_ptr ⋆ frame))
    (exit := fun v (rp_ptr, ap_ptr, bp_ptr, rp_bs, ap_bs, bp_bs, c, frame) st =>
      st.pc = (layout bn_sub_words).label ".Lsub_tail" ∧
      st.data.regs.X3.toNat = num % 2 ∧
      st.data.regs.X0.toBitVec = rp_ptr + BitVec.ofNat 64 (16 * v) ∧
      st.data.regs.X1.toBitVec = ap_ptr + BitVec.ofNat 64 (16 * v) ∧
      st.data.regs.X2.toBitVec = bp_ptr + BitVec.ofNat 64 (16 * v) ∧
      st.data.regs.X30 = s₀.regs.X30 ∧
      st.data.regs.SP = s₀.regs.SP ∧
      st.data.regs.CalleeSavedEq s₀.regs ∧
      ∃ r_pairs : List UInt8,
        r_pairs.length = 16 * v ∧
        Int.ofBytes r_pairs - (if st.data.status.c then 0 else 1) * 256 ^ (16 * v) =
          Int.ofBytes (ap_bs.take (16 * v)) - Int.ofBytes (bp_bs.take (16 * v)) - (if c then 0 else 1) ∧
        (st.data.dmem =⋆
          r_pairs @ rp_ptr ⋆
          (rp_bs.drop (16 * v)) @ (rp_ptr + BitVec.ofNat 64 (16 * v)) ⋆
          ap_bs @ ap_ptr ⋆ bp_bs @ bp_ptr ⋆ frame))
    (measure := num / 2)
    (ghost := (s₀.regs.X0.toBitVec, s₀.regs.X1.toBitVec, s₀.regs.X2.toBitVec, rp, ap, bp, true, R))
    (state := s)
    with v ⟨rp_ptr, ap_ptr, bp_ptr, rp_bs, ap_bs, bp_bs, c, frame⟩
      ⟨hv, h_v_bound, h_x8, h_x3_mod, rfl, rfl, rfl, h_x30, h_sp, h_cs, rfl, h_rp_v, h_ap_v, h_bp_v, h_mem_v⟩
  · kprologue bn_sub_words to ".Lsub_loop" with s₀
    by_cases hn2 : num / 2 = 0
    · have h_shift_zero : (X3.toBitVec >>> 1 = 0#64) :=
        (UInt64.ushiftRight_one_eq_zero_iff X3).mpr (by omega)
      kloop_exit
      refine ⟨by kaddr bn_sub_words, by grind, ?_, ?_, ?_, rfl, rfl,
        Reg64s.CalleeSavedEq_refl _, [], by simp [hn2], by dsimp +zetaDelta only; simp [hn2, Int.ofBytes], ?_⟩
      · simp [hn2]
      · simp [hn2]
      · simp [hn2]
      · simp only [hn2, Nat.mul_zero, List.drop_zero, BitVec.add_zero]
        rw [Mem.At_nil_sep]
        ecancel
    · have h_shift_nz : ¬ (X3.toBitVec >>> 1 = 0#64) := by
        rw [UInt64.ushiftRight_one_eq_zero_iff]; omega
      kloop_next
      exact ⟨by omega, by omega, by grind, by grind,
        rfl, rfl, rfl, rfl, rfl, Reg64s.CalleeSavedEq_refl _, by dsimp +zetaDelta only; simp,
        by omega, by omega, by omega, by ecancel⟩
  · by_cases hv1 : v = 1
    · subst hv1
      kprologue bn_sub_words at ".Lsub_loop" to ".Lsub_tail" with s
      kloop_exit
      refine ⟨by kaddr bn_sub_words, h_x3_mod, by grind, by grind, by grind,
        h_x30, h_sp, h_cs, ?_⟩
      have h_step0 := sbcs_step_bytes (ap_bs.take 8) (bp_bs.take 8) flags.c
        (by simp; omega) (by simp; omega)
      have h_step1 := sbcs_step_bytes ((ap_bs.drop 8).take 8) ((bp_bs.drop 8).take 8)
        (sbcsCarry (ap_bs.take 8) (bp_bs.take 8) flags.c)
        (by simp; omega) (by simp; omega)
      let v0 := (sbcsWord (ap_bs.take 8) (bp_bs.take 8) flags.c).toInt
      let v1 := (sbcsWord ((ap_bs.drop 8).take 8) ((bp_bs.drop 8).take 8)
        (sbcsCarry (ap_bs.take 8) (bp_bs.take 8) flags.c)).toInt
      let c1 := sbcsCarry ((ap_bs.drop 8).take 8) ((bp_bs.drop 8).take 8)
        (sbcsCarry (ap_bs.take 8) (bp_bs.take 8) flags.c)
      refine ⟨Int.toBytes 8 v0 ++ Int.toBytes 8 v1,
        by simp, ?_, by ecancel⟩
      change Int.ofBytes (Int.toBytes 8 v0 ++ Int.toBytes 8 v1) -
        (if c1 then 0 else 1) * 256 ^ (16 * 1) =
        Int.ofBytes (ap_bs.take (16 * 1)) - Int.ofBytes (bp_bs.take (16 * 1)) -
        (if flags.c then 0 else 1)
      rw [Nat.mul_one, Int.ofBytes_append, Int.toBytes_length,
          Int.ofBytes_take_add ap_bs 8 8 (by omega), Int.ofBytes_take_add bp_bs 8 8 (by omega)]
      dsimp +zetaDelta only [v0, v1, c1, sbcsCarry, sbcsWord] at h_step0 h_step1 ⊢
      omega
    · kprologue bn_sub_words at ".Lsub_loop" to ".Lsub_tail" with s
      kstep
      have h_step0 := sbcs_step_bytes (ap_bs.take 8) (bp_bs.take 8) flags.c
        (by simp; omega) (by simp; omega)
      have h_step1 := sbcs_step_bytes ((ap_bs.drop 8).take 8) ((bp_bs.drop 8).take 8)
        (sbcsCarry (ap_bs.take 8) (bp_bs.take 8) flags.c)
        (by simp; omega) (by simp; omega)
      let v0 := (sbcsWord (ap_bs.take 8) (bp_bs.take 8) flags.c).toInt
      let v1 := (sbcsWord ((ap_bs.drop 8).take 8) ((bp_bs.drop 8).take 8)
        (sbcsCarry (ap_bs.take 8) (bp_bs.take 8) flags.c)).toInt
      let c1 := sbcsCarry ((ap_bs.drop 8).take 8) ((bp_bs.drop 8).take 8)
        (sbcsCarry (ap_bs.take 8) (bp_bs.take 8) flags.c)
      have h_w01_len : (Int.toBytes 8 v0 ++ Int.toBytes 8 v1).length = 16 := by simp
      kloop_next (v - 1)
        (X0.toBitVec + 16#64, X1.toBitVec + 16#64, X2.toBitVec + 16#64,
         rp_bs.drop 16, ap_bs.drop 16, bp_bs.drop 16, c1,
         (Int.toBytes 8 v0 ++ Int.toBytes 8 v1) @ X0 ⋆ (ap_bs.take 16) @ X1 ⋆ (bp_bs.take 16) @ X2 ⋆ frame)
      · exact ⟨by omega, by omega, by grind, h_x3_mod,
          by grind, by grind, by grind, h_x30, h_sp, h_cs, rfl,
          by simp [h_rp_v]; omega, by simp [h_ap_v]; omega, by simp [h_bp_v]; omega,
          by ecancel⟩
      rintro t_s ⟨hQ_pc, hQ_x3, hQ_x0, hQ_x1, hQ_x2, hQ_x30, h_sp, h_cs,
        r_rest, h_r_rest_len, h_r_rest_val, hQ_mem⟩
      have h_16_v : 16 + 16 * (v - 1) = 16 * v := by omega
      have h_16_bound : 16 + 16 * (v - 1) ≤ 2 ^ 64 := by omega
      refine ⟨hQ_pc, hQ_x3, ?_, ?_, ?_, hQ_x30, h_sp, h_cs,
        (Int.toBytes 8 v0 ++ Int.toBytes 8 v1) ++ r_rest, by simp; omega, ?_, ?_⟩
      · rw [hQ_x0, BitVec.add_assoc, ← BitVec.ofNat_add, h_16_v]
      · rw [hQ_x1, BitVec.add_assoc, ← BitVec.ofNat_add, h_16_v]
      · rw [hQ_x2, BitVec.add_assoc, ← BitVec.ofNat_add, h_16_v]
      · rw [Int.ofBytes_append, h_w01_len, ← h_16_v,
            Int.ofBytes_take_add ap_bs 16 (16 * (v - 1)) (by omega),
            Int.ofBytes_take_add bp_bs 16 (16 * (v - 1)) (by omega), h_16_v]
        have h_pair_val : Int.ofBytes (Int.toBytes 8 v0 ++ Int.toBytes 8 v1) =
            Int.ofBytes (ap_bs.take 8) + 256 ^ 8 * Int.ofBytes ((ap_bs.drop 8).take 8) -
            (Int.ofBytes (bp_bs.take 8) + 256 ^ 8 * Int.ofBytes ((bp_bs.drop 8).take 8)) -
            (if flags.c then 0 else 1) +
            (if c1 then 0 else 1) * 256 ^ 16 := by
          rw [Int.ofBytes_append, Int.toBytes_length]
          dsimp +zetaDelta only [v0, v1, c1, sbcsCarry, sbcsWord] at h_step0 h_step1 ⊢
          omega
        have h_ap16 : Int.ofBytes (ap_bs.take 16) =
            Int.ofBytes (ap_bs.take 8) + 256 ^ 8 * Int.ofBytes ((ap_bs.drop 8).take 8) :=
          Int.ofBytes_take_add ap_bs 8 8 (by omega)
        have h_bp16 : Int.ofBytes (bp_bs.take 16) =
            Int.ofBytes (bp_bs.take 8) + 256 ^ 8 * Int.ofBytes ((bp_bs.drop 8).take 8) :=
          Int.ofBytes_take_add bp_bs 8 8 (by omega)
        have h_pow := pow_256_16_mul_pred v hv
        have h_mul := congrArg ((256 : Int) ^ 16 * ·) h_r_rest_val
        try dsimp only at h_mul
        rw [Int.mul_sub, Int.mul_sub, Int.mul_left_comm, h_pow] at h_mul
        omega
      · rw [List.drop_drop, show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
            BitVec.add_assoc, ← BitVec.ofNat_add, h_16_v] at hQ_mem
        ecancel
  · obtain ⟨h_x3_mod, h_x0_ptr, h_x1_ptr, h_x2_ptr, h_x30, h_sp, h_cs,
      r_pairs, h_r_pairs_len, h_r_pairs_val, h_mem_q⟩ := hs
    simp only [↓reduceIte, Int.sub_zero] at h_r_pairs_val
    by_cases h_odd : num % 2 = 0
    · kprologue bn_sub_words at ".Lsub_tail" with s
      have h_x3_zero : X3.toBitVec = 0#64 := by grind
      kstep
      kprologue bn_sub_words at ".Lsub_exit"
      kstep
      apply Eventually.done
      have h_16_eq : 16 * (num / 2) = 8 * num := by omega
      have h_ap_take : ap.take (16 * (num / 2)) = ap := List.take_of_length_le (by omega)
      have h_bp_take : bp.take (16 * (num / 2)) = bp := List.take_of_length_le (by omega)
      have h_rp_drop : rp.drop (16 * (num / 2)) = [] := List.drop_eq_nil_of_le (by omega)
      rw [h_rp_drop, Mem.At_nil_sep] at h_mem_q
      refine ⟨by grind, h_sp, h_cs, UInt64.toNat_cset_le_one _,
        r_pairs, by omega, ?_, by ecancel⟩
      change Int.ofBytes r_pairs -
        ((UInt64.ofBitVec (if flags.c then 0#64 else 1#64) : UInt64).toNat : Int) * 256 ^ (8 * num) =
        Int.ofBytes ap - Int.ofBytes bp
      rw [UInt64.toNat_cset_cc]
      rw [h_ap_take, h_bp_take, h_16_eq] at h_r_pairs_val
      omega
    · rw [Mem.At_take_drop_sep ap (16 * (num / 2)) _ (by omega) (by omega),
          Mem.At_take_drop_sep bp (16 * (num / 2)) _ (by omega) (by omega)] at h_mem_q
      kprologue bn_sub_words at ".Lsub_tail" with s
      rw [← h_x0_ptr, ← h_x1_ptr, ← h_x2_ptr] at h_mem_q
      have h_x3_nz : ¬ (X3.toBitVec = 0#64) := by grind
      kstep
      apply Eventually.done
      have h_step_tail := sbcs_step_bytes
        (ap.drop (16 * (num / 2)))
        (bp.drop (16 * (num / 2)))
        flags.c
        (by simp; omega) (by simp; omega)
      let v_tail := (sbcsWord
        (ap.drop (16 * (num / 2)))
        (bp.drop (16 * (num / 2)))
        flags.c).toInt
      let c_tail := sbcsCarry
        (ap.drop (16 * (num / 2)))
        (bp.drop (16 * (num / 2)))
        flags.c
      refine ⟨by grind, h_sp, h_cs, UInt64.toNat_cset_le_one _,
        r_pairs ++ Int.toBytes 8 v_tail, by simp; omega, ?_, ?_⟩
      · change Int.ofBytes (r_pairs ++ Int.toBytes 8 v_tail) -
          ((UInt64.ofBitVec (if c_tail then 0#64 else 1#64) : UInt64).toNat : Int) * 256 ^ (8 * num) =
          Int.ofBytes ap - Int.ofBytes bp
        rw [UInt64.toNat_cset_cc, Int.ofBytes_append, h_r_pairs_len]
        have h_ap_split := Int.ofBytes_take_drop_pair ap (16 * (num / 2)) (by omega)
        have h_bp_split := Int.ofBytes_take_drop_pair bp (16 * (num / 2)) (by omega)
        have h_pow : (256 : Int) ^ (8 * num) = 256 ^ (16 * (num / 2)) * 256 ^ 8 := by
          rw [← Int.pow_add, show 16 * (num / 2) + 8 = 8 * num by omega]
        have h_mul := congrArg ((256 : Int) ^ (16 * (num / 2)) * ·) h_step_tail
        dsimp +zetaDelta only [v_tail, c_tail, sbcsCarry, sbcsWord] at h_mul ⊢
        rw [Int.mul_sub, Int.mul_sub, Int.mul_sub, Int.mul_left_comm, ← h_pow] at h_mul
        rw [Int.mul_comm _ (256 ^ (16 * (num / 2)))] at h_r_pairs_val
        omega
      · rw [Mem.At_take_drop_sep ap (16 * (num / 2)) _ (by omega) (by omega),
            Mem.At_take_drop_sep bp (16 * (num / 2)) _ (by omega) (by omega)]
        simp only [h_x0_ptr, h_x1_ptr, h_x2_ptr] at *
        ecancel


