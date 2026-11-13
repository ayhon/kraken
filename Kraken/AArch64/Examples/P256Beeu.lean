module

import Kraken.AArch64.Parser
import Kraken.AArch64.Semantics
import Kraken.BitVecArith
import Kraken.SeparationMem
import Kraken.SeparationTactics
import Kraken.Tactics
import Kraken.ToBytes

/-!
# Verification of BoringSSL's `beeu_mod_inverse_vartime`

End-to-end functional correctness of the binary extended Euclidean modular inverse
`beeu_mod_inverse_vartime` from BoringSSL's
`third_party/openssl/boringssl/src/gen/bcm/p256_beeu-armv8-asm-linux.S` (stripped of assembler
directives and `AARCH64_SIGN_LINK_REGISTER` / `AARCH64_VALIDATE_LINK_REGISTER` PAC annotations).
-/

open Kraken.AArch64
open Kraken.AArch64.Parser
open Std.ExtHashMap

def beeu_mod_inverse_vartime : Program := ⸨prog|
beeu_mod_inverse_vartime:
    -- Reserve enough space for 14 8-byte registers on the stack
    -- in the first stp call for x29, x30.
    -- Then store the remaining callee-saved registers.
    --
    --    | x29 | x30 | x19 | x20 | ... | x27 | x28 |  x0 |  x2 |
    --    ^                                                     ^
    --    sp  <------------------- 112 bytes ----------------> old sp
    --   x29 (FP)
    --
  stp x29,x30,[sp,#-112]!
  add x29,sp,#0
  stp x19,x20,[sp,#16]
  stp x21,x22,[sp,#32]
  stp x23,x24,[sp,#48]
  stp x25,x26,[sp,#64]
  stp x27,x28,[sp,#80]
  stp x0,x2,[sp,#96]

    -- B = b3..b0 := a
  ldp x25,x26,[x1]
  ldp x27,x28,[x1,#16]

    -- n3..n0 := n
    -- Note: the value of input params are changed in the following.
  ldp x0,x1,[x2]
  ldp x2,x30,[x2,#16]

    -- A = a3..a0 := n
  mov x21, x0
  mov x22, x1
  mov x23, x2
  mov x24, x30

    -- X = x4..x0 := 1
  mov x3, #1
  eor x4, x4, x4
  eor x5, x5, x5
  eor x6, x6, x6
  eor x7, x7, x7

    -- Y = y4..y0 := 0
  eor x8, x8, x8
  eor x9, x9, x9
  eor x10, x10, x10
  eor x11, x11, x11
  eor x12, x12, x12

.Lbeeu_loop:
    -- if B == 0, jump to .Lbeeu_loop_end
  orr x14, x25, x26
  orr x14, x14, x27

    -- reverse the bit order of x25. This is needed for clz after this macro
  rbit x15, x25

  orr x14, x14, x28
  cbz x14,.Lbeeu_loop_end

    -- shift := number of trailing 0s in x25
  orr x15, x15, #1
  clz x13, x15

    -- If there is no shift, goto shift_A_Y
  cbz x13, .Lbeeu_shift_A_Y

    -- Shift B right by x13 bits
  neg x14, x13
  lsr x25, x25, x13
  lsl x15, x26, x14

  lsr x26, x26, x13
  lsl x19, x27, x14

  orr x25, x25, x15

  lsr x27, x27, x13
  lsl x20, x28, x14

  orr x26, x26, x19

  lsr x28, x28, x13

  orr x27, x27, x20

    -- Shift X right by x13 bits, adding n whenever X becomes odd.
  eor x14, x14, x14
.Lbeeu_shift_loop_X:
  tbz x3, #0, .Lshift1_0
  adds x3, x3, x0
  adcs x4, x4, x1
  adcs x5, x5, x2
  adcs x6, x6, x30
  adc x7, x7, x14
.Lshift1_0:
  extr x3, x4, x3, #1
  extr x4, x5, x4, #1
  extr x5, x6, x5, #1
  extr x6, x7, x6, #1
  lsr x7, x7, #1

  subs x13, x13, #1
  bne .Lbeeu_shift_loop_X

.Lbeeu_shift_A_Y:
  rbit x15, x21
  orr x15, x15, #1
  clz x13, x15

  cbz x13, .Lbeeu_update_B_X_or_A_Y

  neg x14, x13
  lsr x21, x21, x13
  lsl x15, x22, x14

  lsr x22, x22, x13
  lsl x19, x23, x14

  orr x21, x21, x15

  lsr x23, x23, x13
  lsl x20, x24, x14

  orr x22, x22, x19

  lsr x24, x24, x13

  orr x23, x23, x20

  eor x14, x14, x14
.Lbeeu_shift_loop_Y:
  tbz x8, #0, .Lshift1_1
  adds x8, x8, x0
  adcs x9, x9, x1
  adcs x10, x10, x2
  adcs x11, x11, x30
  adc x12, x12, x14
.Lshift1_1:
  extr x8, x9, x8, #1
  extr x9, x10, x9, #1
  extr x10, x11, x10, #1
  extr x11, x12, x11, #1
  lsr x12, x12, #1

  subs x13, x13, #1
  bne .Lbeeu_shift_loop_Y

.Lbeeu_update_B_X_or_A_Y:
  subs x14, x25, x21
  sbcs x15, x26, x22
  sbcs x19, x27, x23
  sbcs x20, x28, x24
  bcs .Lbeeu_B_greater_than_A

  subs x21, x21, x25
  sbcs x22, x22, x26
  sbcs x23, x23, x27
  sbcs x24, x24, x28

  adds x8, x8, x3
  adcs x9, x9, x4
  adcs x10, x10, x5
  adcs x11, x11, x6
  adc x12, x12, x7
  b .Lbeeu_loop

.Lbeeu_B_greater_than_A:
  mov x25, x14
  mov x26, x15
  mov x27, x19
  mov x28, x20

  adds x3, x3, x8
  adcs x4, x4, x9
  adcs x5, x5, x10
  adcs x6, x6, x11
  adc x7, x7, x12
  b .Lbeeu_loop

.Lbeeu_loop_end:
  sub x14, x21, #1
  orr x14, x14, x22
  orr x14, x14, x23
  orr x14, x14, x24
  cbnz x14, .Lbeeu_err

.Lbeeu_reduction_loop:
  subs x3, x8, x0
  sbcs x4, x9, x1
  sbcs x5, x10, x2
  sbcs x6, x11, x30
  sbcs x7, x12, x14

  csel x8, x3, x8, cs
  csel x9, x4, x9, cs
  csel x10, x5, x10, cs
  csel x11, x6, x11, cs
  csel x12, x7, x12, cs
  bcs .Lbeeu_reduction_loop

  subs x8, x0, x8
  sbcs x9, x1, x9
  sbcs x10, x2, x10
  sbcs x11, x30, x11

  ldr x3, [sp,#96]
  stp x8, x9, [x3]
  stp x10, x11, [x3,#16]
  mov x0, #1
  b .Lbeeu_finish

.Lbeeu_err:
  eor x0, x0, x0

.Lbeeu_finish:
  add sp,x29,#0
  ldp x19,x20,[sp,#16]
  ldp x21,x22,[sp,#32]
  ldp x23,x24,[sp,#48]
  ldp x25,x26,[sp,#64]
  ldp x27,x28,[sp,#80]
  ldp x29,x30,[sp],#112

  ret
⸩

/-! ## Multi-Limb Representations, Stack Frame Layout, and Loop Invariant -/

/-- 256-bit unsigned integer represented across four 64-bit registers (little-endian limbs). -/
def val256 (w0 w1 w2 w3 : UInt64) : Int :=
  (w0.toNat : Int) +
  256 ^ 8 * (w1.toNat : Int) +
  256 ^ 16 * (w2.toNat : Int) +
  256 ^ 24 * (w3.toNat : Int)

/-- 320-bit unsigned integer represented across five 64-bit registers (little-endian limbs). -/
def val320 (w0 w1 w2 w3 w4 : UInt64) : Int :=
  (w0.toNat : Int) +
  256 ^ 8 * (w1.toNat : Int) +
  256 ^ 16 * (w2.toNat : Int) +
  256 ^ 24 * (w3.toNat : Int) +
  256 ^ 32 * (w4.toNat : Int)

/-- Register-tuple projections for the live 256/320-bit BEEU state in `Reg64s`. -/
abbrev Reg64s.beeuB (r : Reg64s) : Int := val256 r.X25 r.X26 r.X27 r.X28
abbrev Reg64s.beeuA (r : Reg64s) : Int := val256 r.X21 r.X22 r.X23 r.X24
abbrev Reg64s.beeuN (r : Reg64s) : Int := val256 r.X0 r.X1 r.X2 r.X30
abbrev Reg64s.beeuX (r : Reg64s) : Int := val320 r.X3 r.X4 r.X5 r.X6 r.X7
abbrev Reg64s.beeuY (r : Reg64s) : Int := val320 r.X8 r.X9 r.X10 r.X11 r.X12
abbrev Reg64s.beeuY256 (r : Reg64s) : Int := val256 r.X8 r.X9 r.X10 r.X11

/-- The 12 saved callee-saved/frame registers in the `beeu_mod_inverse_vartime` stack frame. -/
def BeeuSavedRegs (r₀ : Reg64s) (sp' : BitVec 64) : DataMem → Prop :=
  (Int.toBytes 8 r₀.X29.toBitVec.toInt) @ sp' ⋆
  (Int.toBytes 8 r₀.X30.toBitVec.toInt) @ (sp' + 8#64) ⋆
  (Int.toBytes 8 r₀.X19.toBitVec.toInt) @ (sp' + 16#64) ⋆
  (Int.toBytes 8 r₀.X20.toBitVec.toInt) @ (sp' + 24#64) ⋆
  (Int.toBytes 8 r₀.X21.toBitVec.toInt) @ (sp' + 32#64) ⋆
  (Int.toBytes 8 r₀.X22.toBitVec.toInt) @ (sp' + 40#64) ⋆
  (Int.toBytes 8 r₀.X23.toBitVec.toInt) @ (sp' + 48#64) ⋆
  (Int.toBytes 8 r₀.X24.toBitVec.toInt) @ (sp' + 56#64) ⋆
  (Int.toBytes 8 r₀.X25.toBitVec.toInt) @ (sp' + 64#64) ⋆
  (Int.toBytes 8 r₀.X26.toBitVec.toInt) @ (sp' + 72#64) ⋆
  (Int.toBytes 8 r₀.X27.toBitVec.toInt) @ (sp' + 80#64) ⋆
  (Int.toBytes 8 r₀.X28.toBitVec.toInt) @ (sp' + 88#64)

/-- The 112-byte stack frame saved by the `beeu_mod_inverse_vartime` prologue. -/
def BeeuStackFrame (r₀ : Reg64s) (sp' : BitVec 64) : DataMem → Prop :=
  BeeuSavedRegs r₀ sp' ⋆
  (Int.toBytes 8 r₀.X0.toBitVec.toInt) @ (sp' + 96#64) ⋆
  (Int.toBytes 8 r₀.X2.toBitVec.toInt) @ (sp' + 104#64)

/-- Four 64-bit limbs stored contiguously in memory at address `p`. -/
def Words256At (w0 w1 w2 w3 : UInt64) (p : BitVec 64) : DataMem → Prop :=
  (Int.toBytes 8 w0.toBitVec.toInt) @ p ⋆
  (Int.toBytes 8 w1.toBitVec.toInt) @ (p + 8#64) ⋆
  (Int.toBytes 8 w2.toBitVec.toInt) @ (p + 16#64) ⋆
  (Int.toBytes 8 w3.toBitVec.toInt) @ (p + 24#64)

/-- Multiplier bounding the accumulators at the top of `.Lbeeu_loop`: `X, Y < 2 · N · beeuBound σ τ`,
where `σ`/`τ` count the halvings of `X`/`Y` performed so far. -/
def beeuBound (σ τ : Nat) : Int := (σ + τ + 2 : Nat)

/-- Loop invariant at the top of `.Lbeeu_loop`, with ghost counters `σ`/`τ` (total halvings of
`X`/`Y` performed so far). Besides the range and modular facts, it bounds the 320-bit accumulators
in every reachable state:
- `2^σ · B ≤ N` and `2^τ · A ≤ N` give `σ, τ ≤ 255` while `B, A > 0`, so `beeuBound σ τ ≤ 512`;
- `X < 2 · N · beeuBound σ τ` (and `X < N · beeuBound σ τ` when `B` is odd, i.e. when `X` has
  already been halved since its last update), symmetrically for `Y`/`A`.
Hence `X, Y < 1024 · N < 2^266`, so `X + N` and `X + Y` never overflow five limbs.
Finally `gcd A B = gcd a N` (Euclid's invariant), so the loop exits with `A = gcd a N`. -/
structure BeeuInv (a N : Int) (σ τ : Nat) (B A X Y : Int) : Prop where
  N_odd : N % 2 = 1
  gcd_eq : Int.gcd A B = Int.gcd a N
  B_nonneg : 0 ≤ B
  B_le : B ≤ N
  A_pos : 0 < A
  A_le : A ≤ N
  X_inv : (a * X - B) % N = 0
  Y_inv : (a * Y + A) % N = 0
  B_shifted : ((2 ^ σ : Nat) : Int) * B ≤ N
  A_shifted : ((2 ^ τ : Nat) : Int) * A ≤ N
  X_lt : X < 2 * (N * beeuBound σ τ)
  X_lt_odd : B % 2 = 1 → X < N * beeuBound σ τ
  Y_lt : Y < 2 * (N * beeuBound σ τ)
  Y_lt_odd : A % 2 = 1 → Y < N * beeuBound σ τ

/-! ## Multi-Limb Arithmetic Lemmas -/

@[simp, ksimp, grind =]
theorem sp_sub_112_mod_16 (sp : BitVec 64) :
    (sp + 18446744073709551504#64) % 16#64 = sp % 16#64 := by
  grind

@[simp, ksimp, grind =]
theorem sp_sub_112_add_zero (sp : BitVec 64) :
    sp + 18446744073709551504#64 + 0#64 = sp + 18446744073709551504#64 := by
  grind

@[simp, ksimp, grind =]
theorem sp_add_112_cancel (sp : BitVec 64) :
    sp + 18446744073709551504#64 + 112#64 = sp := by
  grind

theorem val256_of_limbs (bs : List UInt8) (h : bs.length = 32) :
    val256
      (UInt64.ofBitVec (BitVec.ofInt 64 (Int.ofBytes (bs.take 8))))
      (UInt64.ofBitVec (BitVec.ofInt 64 (Int.ofBytes ((bs.drop 8).take 8))))
      (UInt64.ofBitVec (BitVec.ofInt 64 (Int.ofBytes ((bs.drop 16).take 8))))
      (UInt64.ofBitVec (BitVec.ofInt 64 (Int.ofBytes ((bs.drop 24).take 8)))) =
      Int.ofBytes bs := by
  dsimp only [val256]
  rw [UInt64.toNat_ofBitVec, UInt64.toNat_ofBitVec, UInt64.toNat_ofBitVec, UInt64.toNat_ofBitVec,
      Int.ofBytes_toNat_ofInt_64 _ (by simp [h]),
      Int.ofBytes_toNat_ofInt_64 _ (by simp [h]),
      Int.ofBytes_toNat_ofInt_64 _ (by simp [h]),
      Int.ofBytes_toNat_ofInt_64 _ (by simp [h]),
      Int.ofBytes_32_split bs h]

theorem val256_nonneg (w0 w1 w2 w3 : UInt64) : 0 ≤ val256 w0 w1 w2 w3 := by
  dsimp [val256]; omega

theorem val256_lt (w0 w1 w2 w3 : UInt64) : val256 w0 w1 w2 w3 < 256 ^ 32 := by
  have h0 : w0.toNat < 2 ^ 64 := w0.toBitVec.isLt
  have h1 : w1.toNat < 2 ^ 64 := w1.toBitVec.isLt
  have h2 : w2.toNat < 2 ^ 64 := w2.toBitVec.isLt
  have h3 : w3.toNat < 2 ^ 64 := w3.toBitVec.isLt
  dsimp [val256]; omega

theorem val320_nonneg (w0 w1 w2 w3 w4 : UInt64) : 0 ≤ val320 w0 w1 w2 w3 w4 := by
  dsimp [val320]; omega

theorem val320_lt (w0 w1 w2 w3 w4 : UInt64) : val320 w0 w1 w2 w3 w4 < 256 ^ 40 := by
  have h0 : w0.toNat < 2 ^ 64 := w0.toBitVec.isLt
  have h1 : w1.toNat < 2 ^ 64 := w1.toBitVec.isLt
  have h2 : w2.toNat < 2 ^ 64 := w2.toBitVec.isLt
  have h3 : w3.toNat < 2 ^ 64 := w3.toBitVec.isLt
  have h4 : w4.toNat < 2 ^ 64 := w4.toBitVec.isLt
  dsimp [val320]; omega

theorem val256_eq_zero_limbs (w0 w1 w2 w3 : UInt64) (h : val256 w0 w1 w2 w3 = 0) :
    w0.toBitVec = 0#64 ∧ w1.toBitVec = 0#64 ∧ w2.toBitVec = 0#64 ∧ w3.toBitVec = 0#64 := by
  dsimp [val256] at h
  have hw0 : w0.toNat = 0 := by omega
  have hw1 : w1.toNat = 0 := by omega
  have hw2 : w2.toNat = 0 := by omega
  have hw3 : w3.toNat = 0 := by omega
  refine ⟨BitVec.eq_of_toNat_eq hw0, BitVec.eq_of_toNat_eq hw1,
          BitVec.eq_of_toNat_eq hw2, BitVec.eq_of_toNat_eq hw3⟩

theorem val256_eq_one_limbs (w0 w1 w2 w3 : UInt64) (h : val256 w0 w1 w2 w3 = 1) :
    w0.toBitVec = 1#64 ∧ w1.toBitVec = 0#64 ∧ w2.toBitVec = 0#64 ∧ w3.toBitVec = 0#64 := by
  dsimp [val256] at h
  have hw0 : w0.toNat = 1 := by omega
  have hw1 : w1.toNat = 0 := by omega
  have hw2 : w2.toNat = 0 := by omega
  have hw3 : w3.toNat = 0 := by omega
  refine ⟨BitVec.eq_of_toNat_eq hw0, BitVec.eq_of_toNat_eq hw1,
          BitVec.eq_of_toNat_eq hw2, BitVec.eq_of_toNat_eq hw3⟩

theorem val256_ne_one_or_ne_zero (w0 w1 w2 w3 : UInt64) (h : val256 w0 w1 w2 w3 ≠ 1) :
    ((w0.toBitVec - 1#64 ||| w1.toBitVec ||| w2.toBitVec ||| w3.toBitVec) == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro h_zero
  have ⟨h0, h1, h2, h3⟩ := (or4_sub_one_eq_zero_iff w0.toBitVec w1.toBitVec w2.toBitVec w3.toBitVec).mp h_zero
  apply h
  dsimp [val256]
  have hw0 : w0.toNat = 1 := congrArg BitVec.toNat h0
  have hw1 : w1.toNat = 0 := congrArg BitVec.toNat h1
  have hw2 : w2.toNat = 0 := congrArg BitVec.toNat h2
  have hw3 : w3.toNat = 0 := congrArg BitVec.toNat h3
  omega

theorem val320_lt_256_pow_32 (w0 w1 w2 w3 w4 : UInt64) (h : val320 w0 w1 w2 w3 w4 < 256 ^ 32) :
    w4 = 0 ∧ val256 w0 w1 w2 w3 = val320 w0 w1 w2 w3 w4 := by
  dsimp only [val320, val256] at h ⊢
  have hw4 : w4.toNat = 0 := by omega
  refine ⟨UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hw4), by omega⟩

theorem val256_pos_or_ne_zero (w0 w1 w2 w3 : UInt64) (h : 0 < val256 w0 w1 w2 w3) :
    ((w0.toBitVec ||| w1.toBitVec ||| w2.toBitVec ||| w3.toBitVec) == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro h_zero
  have ⟨h0, h1, h2, h3⟩ := (or4_eq_zero_iff w0.toBitVec w1.toBitVec w2.toBitVec w3.toBitVec).mp h_zero
  have hw0 : w0.toNat = 0 := congrArg BitVec.toNat h0
  have hw1 : w1.toNat = 0 := congrArg BitVec.toNat h1
  have hw2 : w2.toNat = 0 := congrArg BitVec.toNat h2
  have hw3 : w3.toNat = 0 := congrArg BitVec.toNat h3
  dsimp [val256] at h
  omega

theorem shift1_val320 (x0 x1 x2 x3 x4 : UInt64) :
    let w0 := UInt64.ofBitVec (extr1Word x1 x0)
    let w1 := UInt64.ofBitVec (extr1Word x2 x1)
    let w2 := UInt64.ofBitVec (extr1Word x3 x2)
    let w3 := UInt64.ofBitVec (extr1Word x4 x3)
    let w4 := UInt64.ofBitVec (x4.toBitVec >>> 1)
    2 * val320 w0 w1 w2 w3 w4 + (x0.toNat % 2 : Int) = val320 x0 x1 x2 x3 x4 := by
  have h0 := extr1Word_toNat x1 x0
  have h1 := extr1Word_toNat x2 x1
  have h2 := extr1Word_toNat x3 x2
  have h3 := extr1Word_toNat x4 x3
  have h4 := UInt64.toNat_ofBitVec_ushiftRight_one x4
  dsimp only [val320]
  omega

theorem val320_emod_two (x0 x1 x2 x3 x4 : UInt64) :
    val320 x0 x1 x2 x3 x4 % 2 = (x0.toNat % 2 : Int) := by
  dsimp only [val320]; omega

theorem val256_emod_two (x0 x1 x2 x3 : UInt64) :
    val256 x0 x1 x2 x3 % 2 = (x0.toNat % 2 : Int) := by
  dsimp only [val256]; omega

theorem shift256_val256 (b0 b1 b2 b3 : UInt64) (h_nz : ctzClamped b0 ≠ 0#64) :
    let k := ctzClamped b0
    let w0 := UInt64.ofBitVec (shift256Word b0 b1 k)
    let w1 := UInt64.ofBitVec (shift256Word b1 b2 k)
    let w2 := UInt64.ofBitVec (shift256Word b2 b3 k)
    let w3 := UInt64.ofBitVec (shift256TopWord b3 k)
    ((2 ^ k.toNat : Nat) : Int) * val256 w0 w1 w2 w3 = val256 b0 b1 b2 b3 := by
  let k := ctzClamped b0
  have hk63 : k ≤ 63#64 := BitVec.clz_reverse_or_one_le_63 b0.toBitVec
  have hk1 : 1#64 ≤ k := by
    rw [BitVec.le_def]
    have : k.toNat ≠ 0 := fun h0 => h_nz (BitVec.eq_of_toNat_eq h0)
    change 1 ≤ k.toNat
    omega
  have h0 := shift256_limb_toNat b0 b1 k hk1 hk63
  have h1 := shift256_limb_toNat b1 b2 k hk1 hk63
  have h2 := shift256_limb_toNat b2 b3 k hk1 hk63
  have h3 := shift256_top_toNat b3 k hk63
  have hm0 : (b0.toBitVec &&& ((1#64 <<< (k % 64#64)) - 1#64)).toNat = 0 := by
    dsimp +zetaDelta only [ctzClamped]
    rw [BitVec.and_mask_clz_reverse_or_one]
    rfl
  dsimp +zetaDelta only [val256] at h0 h1 h2 h3 ⊢
  rw [hm0] at h0
  grind

/-- If the (clamped) shift amount is zero then `B` is odd. -/
theorem val256_odd_of_ctzClamped_eq_zero (b0 b1 b2 b3 : UInt64)
    (h : ctzClamped b0 = 0#64) : val256 b0 b1 b2 b3 % 2 = 1 := by
  rw [val256_emod_two]
  have h_lsb := BitVec.getLsbD_zero_of_clz_reverse_or_one_eq_zero (by decide) h
  have := UInt64.getLsbD_zero_eq_true_mod2 b0 h_lsb
  omega

/-- If the shifted `B` is still even, the shift was clamped to 63. -/
theorem shift256_val256_even_imp_clamped (b0 b1 b2 b3 : UInt64) :
    let k := ctzClamped b0
    val256 (UInt64.ofBitVec (shift256Word b0 b1 k)) (UInt64.ofBitVec (shift256Word b1 b2 k))
      (UInt64.ofBitVec (shift256Word b2 b3 k)) (UInt64.ofBitVec (shift256TopWord b3 k)) % 2 = 0 →
    k = 63#64 := by
  intro k h
  rw [val256_emod_two] at h
  rcases shift256Word_lsb_or_clamped b0.toBitVec b1.toBitVec with h1 | h1
  · exfalso
    have h2 : (UInt64.ofBitVec (shift256Word b0 b1 k)).toBitVec.getLsbD 0 = true := by
      rw [UInt64.toBitVec_ofBitVec, shift256Word_eq]; exact h1
    have := UInt64.getLsbD_zero_eq_true_mod2 _ h2
    omega
  · exact h1

theorem sub256_step (b0 b1 b2 b3 a0 a1 a2 a3 : UInt64) :
    let c0 := sub0Carry b0 a0
    let c1 := sbcCarry b1 a1 c0
    let c2 := sbcCarry b2 a2 c1
    let c3 := sbcCarry b3 a3 c2
    val256
      (UInt64.ofBitVec (sub0Word b0 a0))
      (UInt64.ofBitVec (sbcWord b1 a1 c0))
      (UInt64.ofBitVec (sbcWord b2 a2 c1))
      (UInt64.ofBitVec (sbcWord b3 a3 c2)) -
      (if c3 then 0 else 1) * 256 ^ 32 =
      val256 b0 b1 b2 b3 - val256 a0 a1 a2 a3 := by
  have h0 := sub0_step b0 a0
  have h1 := sbc_step b1 a1 (sub0Carry b0 a0)
  have h2 := sbc_step b2 a2 (sbcCarry b1 a1 (sub0Carry b0 a0))
  have h3 := sbc_step b3 a3 (sbcCarry b2 a2 (sbcCarry b1 a1 (sub0Carry b0 a0)))
  dsimp only [val256]
  omega

theorem sub256_carry_of_ge (b0 b1 b2 b3 a0 a1 a2 a3 : UInt64)
    (h : val256 b0 b1 b2 b3 ≥ val256 a0 a1 a2 a3) :
    sbcCarry b3 a3 (sbcCarry b2 a2 (sbcCarry b1 a1 (sub0Carry b0 a0))) = true := by
  let c0 := sub0Carry b0 a0
  let c1 := sbcCarry b1 a1 c0
  let c2 := sbcCarry b2 a2 c1
  have h_step := sub256_step b0 b1 b2 b3 a0 a1 a2 a3
  have h_lt := val256_lt
    (UInt64.ofBitVec (sub0Word b0 a0))
    (UInt64.ofBitVec (sbcWord b1 a1 c0))
    (UInt64.ofBitVec (sbcWord b2 a2 c1))
    (UInt64.ofBitVec (sbcWord b3 a3 c2))
  dsimp +zetaDelta only at h_step h_lt
  revert h_step
  cases sbcCarry b3 a3 c2
  · intro h_step; simp only [Bool.false_eq_true, ↓reduceIte] at h_step; omega
  · intro _; rfl

theorem sub256_val_of_ge (b0 b1 b2 b3 a0 a1 a2 a3 : UInt64)
    (h : val256 b0 b1 b2 b3 ≥ val256 a0 a1 a2 a3) :
    let c0 := sub0Carry b0 a0
    let c1 := sbcCarry b1 a1 c0
    let c2 := sbcCarry b2 a2 c1
    val256
      (UInt64.ofBitVec (sub0Word b0 a0))
      (UInt64.ofBitVec (sbcWord b1 a1 c0))
      (UInt64.ofBitVec (sbcWord b2 a2 c1))
      (UInt64.ofBitVec (sbcWord b3 a3 c2)) =
      val256 b0 b1 b2 b3 - val256 a0 a1 a2 a3 := by
  have h_step := sub256_step b0 b1 b2 b3 a0 a1 a2 a3
  dsimp +zetaDelta only at h_step ⊢
  have h_c := sub256_carry_of_ge b0 b1 b2 b3 a0 a1 a2 a3 h
  simp only [h_c, ↓reduceIte] at h_step
  omega

theorem sub256_carry_of_lt (b0 b1 b2 b3 a0 a1 a2 a3 : UInt64)
    (h : val256 b0 b1 b2 b3 < val256 a0 a1 a2 a3) :
    sbcCarry b3 a3 (sbcCarry b2 a2 (sbcCarry b1 a1 (sub0Carry b0 a0))) = false := by
  let c0 := sub0Carry b0 a0
  let c1 := sbcCarry b1 a1 c0
  let c2 := sbcCarry b2 a2 c1
  have h_step := sub256_step b0 b1 b2 b3 a0 a1 a2 a3
  have h_nonneg := val256_nonneg
    (UInt64.ofBitVec (sub0Word b0 a0))
    (UInt64.ofBitVec (sbcWord b1 a1 c0))
    (UInt64.ofBitVec (sbcWord b2 a2 c1))
    (UInt64.ofBitVec (sbcWord b3 a3 c2))
  dsimp +zetaDelta only at h_step h_nonneg
  revert h_step
  cases sbcCarry b3 a3 c2
  · intro _; rfl
  · intro h_step
    simp only [↓reduceIte] at h_step
    omega

theorem add320_val_of_lt (x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 : UInt64)
    (h : val320 x0 x1 x2 x3 x4 + val320 y0 y1 y2 y3 y4 < 256 ^ 40) :
    let c0 := add0Carry x0 y0
    let c1 := adcCarry x1 y1 c0
    let c2 := adcCarry x2 y2 c1
    let c3 := adcCarry x3 y3 c2
    val320
      (UInt64.ofBitVec (add0Word x0 y0))
      (UInt64.ofBitVec (adcWord x1 y1 c0))
      (UInt64.ofBitVec (adcWord x2 y2 c1))
      (UInt64.ofBitVec (adcWord x3 y3 c2))
      (UInt64.ofBitVec (adcWord x4 y4 c3)) =
      val320 x0 x1 x2 x3 x4 + val320 y0 y1 y2 y3 y4 := by
  let c0 := add0Carry x0 y0
  let c1 := adcCarry x1 y1 c0
  let c2 := adcCarry x2 y2 c1
  let c3 := adcCarry x3 y3 c2
  have h0 := add0_step x0 y0
  have h1 := adc_step x1 y1 c0
  have h2 := adc_step x2 y2 c1
  have h3 := adc_step x3 y3 c2
  have h4 := adc_step x4 y4 c3
  have h_nonneg := val320_nonneg
    (UInt64.ofBitVec (add0Word x0 y0))
    (UInt64.ofBitVec (adcWord x1 y1 c0))
    (UInt64.ofBitVec (adcWord x2 y2 c1))
    (UInt64.ofBitVec (adcWord x3 y3 c2))
    (UInt64.ofBitVec (adcWord x4 y4 c3))
  dsimp +zetaDelta only [val320] at h0 h1 h2 h3 h4 h h_nonneg ⊢
  omega

theorem sub320_step (b0 b1 b2 b3 b4 a0 a1 a2 a3 a4 : UInt64) :
    let c0 := sub0Carry b0 a0
    let c1 := sbcCarry b1 a1 c0
    let c2 := sbcCarry b2 a2 c1
    let c3 := sbcCarry b3 a3 c2
    let c4 := sbcCarry b4 a4 c3
    val320
      (UInt64.ofBitVec (sub0Word b0 a0))
      (UInt64.ofBitVec (sbcWord b1 a1 c0))
      (UInt64.ofBitVec (sbcWord b2 a2 c1))
      (UInt64.ofBitVec (sbcWord b3 a3 c2))
      (UInt64.ofBitVec (sbcWord b4 a4 c3)) -
      (if c4 then 0 else 1) * 256 ^ 40 =
      val320 b0 b1 b2 b3 b4 - val320 a0 a1 a2 a3 a4 := by
  let c0 := sub0Carry b0 a0
  let c1 := sbcCarry b1 a1 c0
  let c2 := sbcCarry b2 a2 c1
  let c3 := sbcCarry b3 a3 c2
  have h0 := sub0_step b0 a0
  have h1 := sbc_step b1 a1 c0
  have h2 := sbc_step b2 a2 c1
  have h3 := sbc_step b3 a3 c2
  have h4 := sbc_step b4 a4 c3
  dsimp +zetaDelta only [val320] at h0 h1 h2 h3 h4 ⊢
  omega

theorem sub320_carry_of_ge (b0 b1 b2 b3 b4 a0 a1 a2 a3 a4 : UInt64)
    (h : val320 b0 b1 b2 b3 b4 ≥ val320 a0 a1 a2 a3 a4) :
    sbcCarry b4 a4 (sbcCarry b3 a3 (sbcCarry b2 a2 (sbcCarry b1 a1 (sub0Carry b0 a0)))) = true := by
  let c0 := sub0Carry b0 a0
  let c1 := sbcCarry b1 a1 c0
  let c2 := sbcCarry b2 a2 c1
  let c3 := sbcCarry b3 a3 c2
  have h_step := sub320_step b0 b1 b2 b3 b4 a0 a1 a2 a3 a4
  have h_lt := val320_lt
    (UInt64.ofBitVec (sub0Word b0 a0))
    (UInt64.ofBitVec (sbcWord b1 a1 c0))
    (UInt64.ofBitVec (sbcWord b2 a2 c1))
    (UInt64.ofBitVec (sbcWord b3 a3 c2))
    (UInt64.ofBitVec (sbcWord b4 a4 c3))
  dsimp +zetaDelta only at h_step h_lt
  revert h_step
  cases sbcCarry b4 a4 c3
  · intro h_step; simp only [Bool.false_eq_true, ↓reduceIte] at h_step; omega
  · intro _; rfl

theorem sub320_val_of_ge (b0 b1 b2 b3 b4 a0 a1 a2 a3 a4 : UInt64)
    (h : val320 b0 b1 b2 b3 b4 ≥ val320 a0 a1 a2 a3 a4) :
    let c0 := sub0Carry b0 a0
    let c1 := sbcCarry b1 a1 c0
    let c2 := sbcCarry b2 a2 c1
    let c3 := sbcCarry b3 a3 c2
    val320
      (UInt64.ofBitVec (sub0Word b0 a0))
      (UInt64.ofBitVec (sbcWord b1 a1 c0))
      (UInt64.ofBitVec (sbcWord b2 a2 c1))
      (UInt64.ofBitVec (sbcWord b3 a3 c2))
      (UInt64.ofBitVec (sbcWord b4 a4 c3)) =
      val320 b0 b1 b2 b3 b4 - val320 a0 a1 a2 a3 a4 := by
  have h_step := sub320_step b0 b1 b2 b3 b4 a0 a1 a2 a3 a4
  dsimp +zetaDelta only at h_step ⊢
  have h_c := sub320_carry_of_ge b0 b1 b2 b3 b4 a0 a1 a2 a3 a4 h
  simp only [h_c, ↓reduceIte] at h_step
  omega

/-! ## Loop Invariant and Accumulator Bound Lemmas -/

theorem beeuBound_pos (σ τ : Nat) : 0 < beeuBound σ τ := by
  unfold beeuBound; omega

theorem beeuBound_add (σ τ k₁ k₂ : Nat) :
    beeuBound (σ + k₁) (τ + k₂) = beeuBound σ τ + k₁ + k₂ := by
  unfold beeuBound; omega

theorem beeuBound_le (σ τ : Nat) (hσ : σ ≤ 255) (hτ : τ ≤ 255) :
    beeuBound σ τ ≤ 512 := by
  unfold beeuBound; omega

theorem beeuBound_zero : beeuBound 0 0 = 2 := rfl

/-- After `k ≥ 1` corrected halvings (`p = 2^k`), `X' < N·(M+1)` whenever `X < 2·N·M`. -/
theorem shift_bound_step (X X' N M : Int) (p : Nat) (hp : 2 ≤ p) (hN : 0 ≤ N) (hM : 0 ≤ M)
    (hX : X < 2 * (N * M)) (h : (p : Int) * X' ≤ X + ((p : Int) - 1) * N) : X' < N * (M + 1) := by
  rcases Int.lt_or_le X' (N * (M + 1)) with hlt | hle
  · exact hlt
  exfalso
  have h1 : (p : Int) * (N * (M + 1)) ≤ (p : Int) * X' :=
    Int.mul_le_mul_of_nonneg_left hle (by omega)
  have h2 : 2 * (N * M) ≤ (p : Int) * (N * M) :=
    Int.mul_le_mul_of_nonneg_right (by omega) (Int.mul_nonneg hN hM)
  grind

/-- After a clamped `k = 63` shift, `X₁ < 2·N` whenever `X < 2·N·M` with `M ≤ 512`. -/
theorem shift_clamped_bound (X X₁ N M : Int) (hN : 0 ≤ N) (hM : M ≤ 512)
    (hX : X < 2 * (N * M))
    (h : ((2 ^ 63 : Nat) : Int) * X₁ ≤ X + (((2 ^ 63 : Nat) : Int) - 1) * N) :
    X₁ < N * 2 := by
  have hM_le : N * M ≤ N * 512 := Int.mul_le_mul_of_nonneg_left hM hN
  rcases Int.lt_or_le X₁ (N * 2) with hlt | hle
  · exact hlt
  exfalso
  have h1 : ((2 ^ 63 : Nat) : Int) * (N * 2) ≤ ((2 ^ 63 : Nat) : Int) * X₁ :=
    Int.mul_le_mul_of_nonneg_left hle (by decide)
  omega

theorem update_bound_even (X₁ Y₁ N M M₂ : Int) (k₁ k₂ : Nat) (hN : 0 ≤ N)
    (hX : X₁ < N * (M + k₁)) (hY : Y₁ < N * (M + k₂)) (hM₂ : M + k₁ + k₂ ≤ M₂) :
    X₁ + Y₁ < 2 * (N * M₂) := by
  have : N * (M + k₁ + (M + k₂)) ≤ N * (2 * M₂) :=
    Int.mul_le_mul_of_nonneg_left (by omega) hN
  grind

/-- When the difference after the shift phase is odd, at least one shift was clamped (`k₁ = 63` or
`k₂ = 63`), resetting that accumulator below `2·N` while increasing `beeuBound` by at least `63`,
so `X₁ + Y₁ < N · (M + k₁ + k₂)` without doubling `M`. -/
theorem update_bound_clamped (X X₁ Y Y₁ N M M₂ : Int) (k₁ k₂ : Nat)
    (hN : 0 ≤ N) (hM_le : M ≤ 512)
    (hX : X < 2 * (N * M)) (hY : Y < 2 * (N * M))
    (hX₁ : X₁ < N * (M + k₁)) (hY₁ : Y₁ < N * (M + k₂))
    (hX_bnd : ((2 ^ k₁ : Nat) : Int) * X₁ ≤ X + (((2 ^ k₁ : Nat) : Int) - 1) * N)
    (hY_bnd : ((2 ^ k₂ : Nat) : Int) * Y₁ ≤ Y + (((2 ^ k₂ : Nat) : Int) - 1) * N)
    (hclamp : k₁ = 63 ∨ k₂ = 63) (hM₂ : M + k₁ + k₂ ≤ M₂) :
    X₁ + Y₁ < N * M₂ := by
  rcases hclamp with rfl | rfl
  · have hX2 := shift_clamped_bound X X₁ N M hN hM_le hX hX_bnd
    have : N * (2 + (M + k₂)) ≤ N * M₂ :=
      Int.mul_le_mul_of_nonneg_left (by omega) hN
    grind
  · have hY2 := shift_clamped_bound Y Y₁ N M hN hM_le hY hY_bnd
    have : N * ((M + k₁) + 2) ≤ N * M₂ :=
      Int.mul_le_mul_of_nonneg_left (by omega) hN
    grind

theorem bound_mono_right (N M M' Z : Int) (hN : 0 ≤ N) (h : Z < N * M) (hM : M ≤ M') : Z < N * M' := by
  have := Int.mul_le_mul_of_nonneg_left hM hN
  omega

theorem two_pow_le_imp_le_255 (σ : Nat) (N : Int) (h : ((2 ^ σ : Nat) : Int) ≤ N)
    (hN : N < 256 ^ 32) : σ ≤ 255 := by
  have h256 : ((2 ^ 256 : Nat) : Int) = 256 ^ 32 := by decide
  have h1 : ((2 ^ σ : Nat) : Int) < ((2 ^ 256 : Nat) : Int) := by rw [h256]; omega
  have h2 : (2 ^ σ : Nat) < 2 ^ 256 := by exact_mod_cast h1
  have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h2
  omega

theorem BeeuInv.sigma_le {a N : Int} {σ τ : Nat} {B A X Y : Int}
    (h : BeeuInv a N σ τ B A X Y) (hB : 0 < B) (hN : N < 256 ^ 32) : σ ≤ 255 := by
  have h0 : (0 : Int) ≤ ((2 ^ σ : Nat) : Int) := by exact_mod_cast Nat.zero_le _
  have h1 := Int.mul_le_mul_of_nonneg_left (show (1 : Int) ≤ B by omega) h0
  have h2 := h.B_shifted
  exact two_pow_le_imp_le_255 σ N (by omega) hN

theorem BeeuInv.tau_le {a N : Int} {σ τ : Nat} {B A X Y : Int}
    (h : BeeuInv a N σ τ B A X Y) (hN : N < 256 ^ 32) : τ ≤ 255 := by
  have h0 : (0 : Int) ≤ ((2 ^ τ : Nat) : Int) := by exact_mod_cast Nat.zero_le _
  have h1 := Int.mul_le_mul_of_nonneg_left (show (1 : Int) ≤ A by have := h.A_pos; omega) h0
  have h2 := h.A_shifted
  exact two_pow_le_imp_le_255 τ N (by omega) hN

/-- The absolute bounds needed by the per-phase lemmas: `X, Y < 2^319`. -/
theorem BeeuInv.bounds {a N : Int} {σ τ : Nat} {B A X Y : Int}
    (h : BeeuInv a N σ τ B A X Y) (hB : 0 < B) (hN : N < 256 ^ 32) :
    X < 256 ^ 40 / 2 ∧ Y < 256 ^ 40 / 2 ∧ beeuBound σ τ ≤ 512 := by
  have hσ := h.sigma_le hB hN
  have hτ := h.tau_le hN
  have hM := beeuBound_le σ τ hσ hτ
  have hN0 : 0 ≤ N := by have := h.A_pos; have := h.A_le; omega
  have h1 : N * beeuBound σ τ ≤ N * 512 := Int.mul_le_mul_of_nonneg_left hM hN0
  have hX := h.X_lt
  have hY := h.Y_lt
  exact ⟨by omega, by omega, hM⟩

/-- Bound on `X` (resp. `Y`) right after its shift phase, in terms of the loop-top multiplier `M`:
`X₁ < N·(M + k)` whenever `X < 2·N·M`, `(B odd → X < N·M)`, `(B even → 1 ≤ k)` and
`2^k·X₁ ≤ X + (2^k − 1)·N`. -/
theorem shift_phase_bound (X X₁ N M B : Int) (k : Nat) (hN : 0 ≤ N) (hM : 0 ≤ M)
    (hX : X < 2 * (N * M)) (hX_odd : B % 2 = 1 → X < N * M)
    (hk : B % 2 = 0 → 1 ≤ k)
    (h : ((2 ^ k : Nat) : Int) * X₁ ≤ X + (((2 ^ k : Nat) : Int) - 1) * N) :
    X₁ < N * (M + k) := by
  by_cases hk0 : k = 0
  · subst hk0
    simp only [Nat.pow_zero, Int.natCast_one, Int.one_mul, Int.sub_self, Int.zero_mul,
      Int.add_zero, Int.natCast_zero] at h ⊢
    have hB : B % 2 = 1 := by
      have h01 : B % 2 = 0 ∨ B % 2 = 1 := by omega
      rcases h01 with h0 | h1
      · exact absurd (hk h0) (by omega)
      · exact h1
    have := hX_odd hB
    omega
  · have hp : 2 ≤ 2 ^ k := Nat.one_lt_two_pow hk0
    have h1 := shift_bound_step X X₁ N M (2 ^ k) hp hN hM hX h
    exact bound_mono_right N (M + 1) (M + k) X₁ hN h1 (by omega)

theorem shift_B_X_mod_inv (k : Nat) (a B B' X X' n : Int)
    (hn_odd : n % 2 = 1)
    (hB : ((2 ^ k : Nat) : Int) * B' = B)
    (hX : (((2 ^ k : Nat) : Int) * X') % n = X % n)
    (h_inv : (a * X - B) % n = 0) :
    (a * X' - B') % n = 0 := by
  apply pow2_mul_emod_eq_zero_of_odd k (a * X' - B') n hn_odd
  have h_lin : ((2 ^ k : Nat) : Int) * (a * X' - B') =
      a * (((2 ^ k : Nat) : Int) * X') - B := by
    rw [← hB]; grind
  rw [h_lin, Int.sub_emod, Int.mul_emod a, hX, ← Int.mul_emod, ← Int.sub_emod, h_inv]

theorem shift_A_Y_mod_inv (k : Nat) (a A A' Y Y' n : Int)
    (hn_odd : n % 2 = 1)
    (hA : ((2 ^ k : Nat) : Int) * A' = A)
    (hY : (((2 ^ k : Nat) : Int) * Y') % n = Y % n)
    (h_inv : (a * Y + A) % n = 0) :
    (a * Y' + A') % n = 0 := by
  simpa [Int.sub_neg] using
    shift_B_X_mod_inv k a (-A) (-A') Y Y' n hn_odd (by grind) hY (by simpa [Int.sub_neg] using h_inv)

theorem mod_inv_of_beeu_end (a y out n : Int)
    (hn_pos : 0 < n)
    (h_inv : (a * y + 1) % n = 0)
    (h_out : out = n - (y % n)) :
    0 < out ∧ out ≤ n ∧ (a * out) % n = 1 % n := by
  have hy_nonneg : 0 ≤ y % n := Int.emod_nonneg y (by omega)
  have hy_lt : y % n < n := Int.emod_lt_of_pos y hn_pos
  refine ⟨by omega, by omega, ?_⟩
  have h_sub_mod : (y - y % n) % n = 0 := by
    rw [Int.sub_emod, Int.emod_emod, Int.sub_self, Int.zero_emod]
  obtain ⟨q, hq⟩ : n ∣ a * y + 1 := Int.dvd_of_emod_eq_zero h_inv
  obtain ⟨k, hk⟩ : n ∣ y - y % n := Int.dvd_of_emod_eq_zero h_sub_mod
  have h_eq : a * out = 1 + (a - q + a * k) * n := by
    rw [h_out]; grind
  rw [h_eq, Int.add_emod, Int.mul_emod, Int.emod_self, Int.mul_zero,
    Int.zero_emod, Int.add_zero, Int.emod_emod]

/-! ## Inner Shift Loop & `SHIFT256` Block Specifications -/

block_spec beeu_shift_loop_X_pre_correct beeu_mod_inverse_vartime s
  from ".Lbeeu_shift_loop_X" to ".Lshift1_0"
  (writes := [beeuX])
  (pre :=
    s.regs.X14 = 0 ∧
    s.regs.beeuN % 2 = 1 ∧
    s.regs.beeuX + s.regs.beeuN < 256 ^ 40)
  (post := fun st =>
    st.data.dmem = s.dmem ∧
    st.data.regs.beeuX % 2 = 0 ∧
    st.data.regs.beeuX % s.regs.beeuN = s.regs.beeuX % s.regs.beeuN ∧
    st.data.regs.beeuX ≤ s.regs.beeuX + s.regs.beeuN) := by
  rintro ⟨h14, hN_odd, h_xn_lt⟩
  dsimp only [Reg64s.beeuX, Reg64s.beeuN] at hN_odd h_xn_lt ⊢
  kprologue beeu_mod_inverse_vartime at ".Lbeeu_shift_loop_X" to ".Lshift1_0" with s
  cases h_lsb : X3.toBitVec.getLsbD 0
  · have h_mod2 := UInt64.getLsbD_zero_eq_false_mod2 X3 h_lsb
    have := val256_nonneg X0 X1 X2 X30
    kfinish beeu_mod_inverse_vartime
    rw [val320_emod_two]; omega
  · have h_mod2 := UInt64.getLsbD_zero_eq_true_mod2 X3 h_lsb
    have h0 : (0 : UInt64).toNat = 0 := rfl
    have h_lt320 : val320 X3 X4 X5 X6 X7 + val320 X0 X1 X2 X30 X14 < 256 ^ 40 := by
      subst h14; dsimp only [val320, val256] at h_xn_lt ⊢; omega
    have h_add := add320_val_of_lt X3 X4 X5 X6 X7 X0 X1 X2 X30 X14 h_lt320
    have h_n320 : val320 X0 X1 X2 X30 X14 = val256 X0 X1 X2 X30 := by
      subst h14; dsimp only [val320, val256]; omega
    kfinish beeu_mod_inverse_vartime [add0Carry, adcCarry, add0Word, adcWord]
    · rw [h_add, h_n320]
      have hx := val320_emod_two X3 X4 X5 X6 X7
      omega
    · rw [h_add, h_n320, Int.add_emod, Int.emod_self, Int.add_zero, Int.emod_emod]

block_spec beeu_shift1_0_correct beeu_mod_inverse_vartime s
  from ".Lshift1_0"
  (exit := if s.regs.X13.toNat = 1 then
      (layout beeu_mod_inverse_vartime).label ".Lbeeu_shift_A_Y"
    else
      (layout beeu_mod_inverse_vartime).label ".Lbeeu_shift_loop_X")
  (writes := [beeuX, X13])
  (pre :=
    0 < s.regs.X13.toNat ∧
    s.regs.beeuX % 2 = 0)
  (post := fun st =>
    st.data.dmem = s.dmem ∧
    st.data.regs.X13.toNat = s.regs.X13.toNat - 1 ∧
    2 * st.data.regs.beeuX = s.regs.beeuX) := by
  rintro ⟨h_x13_pos, h_x_even⟩
  dsimp only [Reg64s.beeuX] at h_x_even ⊢
  by_cases h1 : s.regs.X13.toNat = 1
  · simp only [h1, ↓reduceIte]
    kprologue beeu_mod_inverse_vartime at ".Lshift1_0" to ".Lbeeu_shift_A_Y" with s
    have h_x13_bv : X13.toBitVec = 1#64 := BitVec.eq_of_toNat_eq h1
    have h_shift := shift1_val320 X3 X4 X5 X6 X7
    have h_x3_mod : (X3.toNat % 2 : Int) = 0 := by
      rw [← val320_emod_two X3 X4 X5 X6 X7]; exact h_x_even
    kfinish beeu_mod_inverse_vartime [extr_sem_eq]
  · simp only [h1, ↓reduceIte]
    have h_gt1 : 1 < s.regs.X13.toNat := by omega
    kprologue beeu_mod_inverse_vartime at ".Lshift1_0" to ".Lbeeu_shift_A_Y" with s
    have h_nz := sub_one_beq_zero_false_of_gt_one X13 h_gt1
    have h_dec := toNat_sub_one_of_pos X13 h_x13_pos
    have h_shift := shift1_val320 X3 X4 X5 X6 X7
    have h_x3_mod : (X3.toNat % 2 : Int) = 0 := by
      rw [← val320_emod_two X3 X4 X5 X6 X7]; exact h_x_even
    kfinish beeu_mod_inverse_vartime [extr_sem_eq]

block_spec beeu_shift_loop_X_step_correct beeu_mod_inverse_vartime s
  from ".Lbeeu_shift_loop_X"
  (exit := if s.regs.X13.toNat = 1 then
      (layout beeu_mod_inverse_vartime).label ".Lbeeu_shift_A_Y"
    else
      (layout beeu_mod_inverse_vartime).label ".Lbeeu_shift_loop_X")
  (writes := [beeuX, X13])
  (pre :=
    0 < s.regs.X13.toNat ∧
    s.regs.X14 = 0 ∧
    s.regs.beeuN % 2 = 1 ∧
    s.regs.beeuX + s.regs.beeuN < 256 ^ 40)
  (post := fun st =>
    st.data.dmem = s.dmem ∧
    st.data.regs.X13.toNat = s.regs.X13.toNat - 1 ∧
    (2 * st.data.regs.beeuX) % s.regs.beeuN = s.regs.beeuX % s.regs.beeuN ∧
    2 * st.data.regs.beeuX ≤ s.regs.beeuX + s.regs.beeuN) := by
  rintro ⟨h_x13_pos, h14, hN_odd, h_xn_lt⟩
  kcall beeu_shift_loop_X_pre_correct s ⟨h14, hN_odd, h_xn_lt⟩
    with mid ⟨h_fr, h_dmem, h_even, h_mod, h_le⟩
  kframe_eqs h_fr
  kcall beeu_shift1_0_correct mid ⟨h_fr_X13.symm ▸ h_x13_pos, h_even⟩
    with fin ⟨h_fr', h_dmem', h_x13', h_2x⟩
  apply Eventually.done
  dsimp only
  rw [h_fr_X13] at h_x13' ⊢
  refine ⟨rfl, by kframe, h_dmem'.trans h_dmem, h_x13', ?_, ?_⟩
  · rw [h_2x, h_mod]
  · omega

block_spec beeu_shift_loop_X_correct beeu_mod_inverse_vartime s
  from ".Lbeeu_shift_loop_X" to ".Lbeeu_shift_A_Y"
  (writes := [beeuX, X13])
  (pre :=
    0 < s.regs.X13.toNat ∧
    s.regs.X14 = 0 ∧
    s.regs.beeuN % 2 = 1 ∧
    s.regs.beeuX + s.regs.beeuN < 256 ^ 40)
  (post := fun st =>
    st.data.dmem = s.dmem ∧
    (((2 ^ s.regs.X13.toNat : Nat) : Int) * st.data.regs.beeuX) % s.regs.beeuN =
      s.regs.beeuX % s.regs.beeuN ∧
    st.data.regs.beeuX < 256 ^ 40 / 2 ∧
    ((2 ^ s.regs.X13.toNat : Nat) : Int) * st.data.regs.beeuX ≤
      s.regs.beeuX + (((2 ^ s.regs.X13.toNat : Nat) : Int) - 1) * s.regs.beeuN) := by
  rintro ⟨h_x13_pos, h14, hN_odd, h_xn_lt⟩
  let k₀ := s.regs.X13.toNat
  have h_N_lt : s.regs.beeuN < 256 ^ 32 := val256_lt _ _ _ _
  kloop at ".Lbeeu_shift_loop_X" (writes := [beeuX, X13])
    (inv := fun v st =>
      st.data.dmem = s.dmem ∧
      0 < v ∧ v ≤ k₀ ∧
      st.data.regs.X13.toNat = v ∧
      st.data.regs.beeuX + s.regs.beeuN < 256 ^ 40 ∧
      (((2 ^ (k₀ - v) : Nat) : Int) * st.data.regs.beeuX) % s.regs.beeuN =
        s.regs.beeuX % s.regs.beeuN ∧
      ((2 ^ (k₀ - v) : Nat) : Int) * st.data.regs.beeuX ≤
        s.regs.beeuX + (((2 ^ (k₀ - v) : Nat) : Int) - 1) * s.regs.beeuN)
    (measure := k₀)
    with v _ ⟨h_dmem, hv_pos, hv_le, h_x13, h_xn, h_inv, h_bnd⟩
  · refine ⟨rfl, h_x13_pos, Nat.le_refl _, rfl, h_xn_lt, ?_, ?_⟩
    · simp
    · simp
  · kcall beeu_shift_loop_X_step_correct st
        ⟨h_x13 ▸ hv_pos, h_fr_X14.trans h14, h_fr_beeuN.symm ▸ hN_odd, h_fr_beeuN.symm ▸ h_xn⟩
      with mid ⟨h_fr', h_dmem', h_x13', h_mod', h_2x'⟩
    rw [h_x13] at h_x13' ⊢
    rw [h_fr_beeuN] at h_mod' h_2x'
    have h_step := pow2_mul_emod_step (k₀ - v) _ _ _ _ h_inv h_mod'
    have h_bstep := pow2_mul_bound_step (k₀ - v) _ _ _ _ h_bnd h_2x'
    by_cases hv1 : v = 1
    · simp only [hv1, ↓reduceIte]
      have h_k : k₀ - v + 1 = k₀ := by omega
      rw [h_k] at h_step h_bstep
      kloop_exit
      exact ⟨rfl, by kframe, h_dmem'.trans h_dmem, h_step, by omega, h_bstep⟩
    · simp only [hv1, ↓reduceIte]
      have h_k : k₀ - v + 1 = k₀ - (v - 1) := by omega
      rw [h_k] at h_step h_bstep
      kloop_next (v - 1)
      exact ⟨h_dmem'.trans h_dmem, by omega, by omega, h_x13', by omega,
        h_step, h_bstep⟩

block_spec beeu_shift_loop_Y_pre_correct beeu_mod_inverse_vartime s
  from ".Lbeeu_shift_loop_Y" to ".Lshift1_1"
  (writes := [beeuY])
  (pre :=
    s.regs.X14 = 0 ∧
    s.regs.beeuN % 2 = 1 ∧
    s.regs.beeuY + s.regs.beeuN < 256 ^ 40)
  (post := fun st =>
    st.data.dmem = s.dmem ∧
    st.data.regs.beeuY % 2 = 0 ∧
    st.data.regs.beeuY % s.regs.beeuN = s.regs.beeuY % s.regs.beeuN ∧
    st.data.regs.beeuY ≤ s.regs.beeuY + s.regs.beeuN) := by
  rintro ⟨h14, hN_odd, h_yn_lt⟩
  dsimp only [Reg64s.beeuY, Reg64s.beeuN] at hN_odd h_yn_lt ⊢
  kprologue beeu_mod_inverse_vartime at ".Lbeeu_shift_loop_Y" to ".Lshift1_1" with s
  cases h_lsb : X8.toBitVec.getLsbD 0
  · have h_mod2 := UInt64.getLsbD_zero_eq_false_mod2 X8 h_lsb
    have := val256_nonneg X0 X1 X2 X30
    kfinish beeu_mod_inverse_vartime
    rw [val320_emod_two]; omega
  · have h_mod2 := UInt64.getLsbD_zero_eq_true_mod2 X8 h_lsb
    have h0 : (0 : UInt64).toNat = 0 := rfl
    have h_lt320 : val320 X8 X9 X10 X11 X12 + val320 X0 X1 X2 X30 X14 < 256 ^ 40 := by
      subst h14; dsimp only [val320, val256] at h_yn_lt ⊢; omega
    have h_add := add320_val_of_lt X8 X9 X10 X11 X12 X0 X1 X2 X30 X14 h_lt320
    have h_n320 : val320 X0 X1 X2 X30 X14 = val256 X0 X1 X2 X30 := by
      subst h14; dsimp only [val320, val256]; omega
    kfinish beeu_mod_inverse_vartime [add0Carry, adcCarry, add0Word, adcWord]
    · rw [h_add, h_n320]
      have hy := val320_emod_two X8 X9 X10 X11 X12
      omega
    · rw [h_add, h_n320, Int.add_emod, Int.emod_self, Int.add_zero, Int.emod_emod]

block_spec beeu_shift1_1_correct beeu_mod_inverse_vartime s
  from ".Lshift1_1"
  (exit := if s.regs.X13.toNat = 1 then
      (layout beeu_mod_inverse_vartime).label ".Lbeeu_update_B_X_or_A_Y"
    else
      (layout beeu_mod_inverse_vartime).label ".Lbeeu_shift_loop_Y")
  (writes := [beeuY, X13])
  (pre :=
    0 < s.regs.X13.toNat ∧
    s.regs.beeuY % 2 = 0)
  (post := fun st =>
    st.data.dmem = s.dmem ∧
    st.data.regs.X13.toNat = s.regs.X13.toNat - 1 ∧
    2 * st.data.regs.beeuY = s.regs.beeuY) := by
  rintro ⟨h_x13_pos, h_y_even⟩
  dsimp only [Reg64s.beeuY] at h_y_even ⊢
  by_cases h1 : s.regs.X13.toNat = 1
  · simp only [h1, ↓reduceIte]
    kprologue beeu_mod_inverse_vartime at ".Lshift1_1" to ".Lbeeu_update_B_X_or_A_Y" with s
    have h_x13_bv : X13.toBitVec = 1#64 := BitVec.eq_of_toNat_eq h1
    have h_shift := shift1_val320 X8 X9 X10 X11 X12
    have h_x8_mod : (X8.toNat % 2 : Int) = 0 := by
      rw [← val320_emod_two X8 X9 X10 X11 X12]; exact h_y_even
    kfinish beeu_mod_inverse_vartime [extr_sem_eq]
  · simp only [h1, ↓reduceIte]
    have h_gt1 : 1 < s.regs.X13.toNat := by omega
    kprologue beeu_mod_inverse_vartime at ".Lshift1_1" to ".Lbeeu_update_B_X_or_A_Y" with s
    have h_nz := sub_one_beq_zero_false_of_gt_one X13 h_gt1
    have h_dec := toNat_sub_one_of_pos X13 h_x13_pos
    have h_shift := shift1_val320 X8 X9 X10 X11 X12
    have h_x8_mod : (X8.toNat % 2 : Int) = 0 := by
      rw [← val320_emod_two X8 X9 X10 X11 X12]; exact h_y_even
    kfinish beeu_mod_inverse_vartime [extr_sem_eq]

block_spec beeu_shift_loop_Y_step_correct beeu_mod_inverse_vartime s
  from ".Lbeeu_shift_loop_Y"
  (exit := if s.regs.X13.toNat = 1 then
      (layout beeu_mod_inverse_vartime).label ".Lbeeu_update_B_X_or_A_Y"
    else
      (layout beeu_mod_inverse_vartime).label ".Lbeeu_shift_loop_Y")
  (writes := [beeuY, X13])
  (pre :=
    0 < s.regs.X13.toNat ∧
    s.regs.X14 = 0 ∧
    s.regs.beeuN % 2 = 1 ∧
    s.regs.beeuY + s.regs.beeuN < 256 ^ 40)
  (post := fun st =>
    st.data.dmem = s.dmem ∧
    st.data.regs.X13.toNat = s.regs.X13.toNat - 1 ∧
    (2 * st.data.regs.beeuY) % s.regs.beeuN = s.regs.beeuY % s.regs.beeuN ∧
    2 * st.data.regs.beeuY ≤ s.regs.beeuY + s.regs.beeuN) := by
  rintro ⟨h_x13_pos, h14, hN_odd, h_yn_lt⟩
  kcall beeu_shift_loop_Y_pre_correct s ⟨h14, hN_odd, h_yn_lt⟩
    with mid ⟨h_fr, h_dmem, h_even, h_mod, h_le⟩
  kframe_eqs h_fr
  kcall beeu_shift1_1_correct mid ⟨h_fr_X13.symm ▸ h_x13_pos, h_even⟩
    with fin ⟨h_fr', h_dmem', h_x13', h_2y⟩
  apply Eventually.done
  dsimp only
  rw [h_fr_X13] at h_x13' ⊢
  refine ⟨rfl, by kframe, h_dmem'.trans h_dmem, h_x13', ?_, ?_⟩
  · rw [h_2y, h_mod]
  · omega

block_spec beeu_shift_loop_Y_correct beeu_mod_inverse_vartime s
  from ".Lbeeu_shift_loop_Y" to ".Lbeeu_update_B_X_or_A_Y"
  (writes := [beeuY, X13])
  (pre :=
    0 < s.regs.X13.toNat ∧
    s.regs.X14 = 0 ∧
    s.regs.beeuN % 2 = 1 ∧
    s.regs.beeuY + s.regs.beeuN < 256 ^ 40)
  (post := fun st =>
    st.data.dmem = s.dmem ∧
    (((2 ^ s.regs.X13.toNat : Nat) : Int) * st.data.regs.beeuY) % s.regs.beeuN =
      s.regs.beeuY % s.regs.beeuN ∧
    st.data.regs.beeuY < 256 ^ 40 / 2 ∧
    ((2 ^ s.regs.X13.toNat : Nat) : Int) * st.data.regs.beeuY ≤
      s.regs.beeuY + (((2 ^ s.regs.X13.toNat : Nat) : Int) - 1) * s.regs.beeuN) := by
  rintro ⟨h_x13_pos, h14, hN_odd, h_yn_lt⟩
  let k₀ := s.regs.X13.toNat
  have h_N_lt : s.regs.beeuN < 256 ^ 32 := val256_lt _ _ _ _
  kloop at ".Lbeeu_shift_loop_Y" (writes := [beeuY, X13])
    (inv := fun v st =>
      st.data.dmem = s.dmem ∧
      0 < v ∧ v ≤ k₀ ∧
      st.data.regs.X13.toNat = v ∧
      st.data.regs.beeuY + s.regs.beeuN < 256 ^ 40 ∧
      (((2 ^ (k₀ - v) : Nat) : Int) * st.data.regs.beeuY) % s.regs.beeuN =
        s.regs.beeuY % s.regs.beeuN ∧
      ((2 ^ (k₀ - v) : Nat) : Int) * st.data.regs.beeuY ≤
        s.regs.beeuY + (((2 ^ (k₀ - v) : Nat) : Int) - 1) * s.regs.beeuN)
    (measure := k₀)
    with v _ ⟨h_dmem, hv_pos, hv_le, h_x13, h_yn, h_inv, h_bnd⟩
  · refine ⟨rfl, h_x13_pos, Nat.le_refl _, rfl, h_yn_lt, ?_, ?_⟩
    · simp
    · simp
  · kcall beeu_shift_loop_Y_step_correct st
        ⟨h_x13 ▸ hv_pos, h_fr_X14.trans h14, h_fr_beeuN.symm ▸ hN_odd, h_fr_beeuN.symm ▸ h_yn⟩
      with mid ⟨h_fr', h_dmem', h_x13', h_mod', h_2y'⟩
    rw [h_x13] at h_x13' ⊢
    rw [h_fr_beeuN] at h_mod' h_2y'
    have h_step := pow2_mul_emod_step (k₀ - v) _ _ _ _ h_inv h_mod'
    have h_bstep := pow2_mul_bound_step (k₀ - v) _ _ _ _ h_bnd h_2y'
    by_cases hv1 : v = 1
    · simp only [hv1, ↓reduceIte]
      have h_k : k₀ - v + 1 = k₀ := by omega
      rw [h_k] at h_step h_bstep
      kloop_exit
      exact ⟨rfl, by kframe, h_dmem'.trans h_dmem, h_step, by omega, h_bstep⟩
    · simp only [hv1, ↓reduceIte]
      have h_k : k₀ - v + 1 = k₀ - (v - 1) := by omega
      rw [h_k] at h_step h_bstep
      kloop_next (v - 1)
      exact ⟨h_dmem'.trans h_dmem, by omega, by omega, h_x13', by omega,
        h_step, h_bstep⟩

block_spec beeu_shift_B_header_correct beeu_mod_inverse_vartime s
  from ".Lbeeu_loop"
  (writes := [beeuB, X13, X14, X15, X19, X20])
  (pre := 0 < s.regs.beeuB)
  (post := fun st =>
    let k := ctzClamped s.regs.X25
    st.data.dmem = s.dmem ∧
    if k = 0#64 then
      st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_shift_A_Y" ∧
      st.data.regs.beeuB = s.regs.beeuB ∧
      s.regs.beeuB % 2 = 1
    else
      st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_shift_loop_X" ∧
      st.data.regs.X13.toNat = k.toNat ∧
      0 < k.toNat ∧
      st.data.regs.X14 = 0 ∧
      ((2 ^ k.toNat : Nat) : Int) * st.data.regs.beeuB = s.regs.beeuB ∧
      (st.data.regs.beeuB % 2 = 0 → k = 63#64)) := by
  intro hB_pos
  by_cases hk : ctzClamped s.regs.X25 = 0#64
  · simp only [hk, ↓reduceIte]
    have h_odd := val256_odd_of_ctzClamped_eq_zero s.regs.X25 s.regs.X26 s.regs.X27 s.regs.X28 hk
    dsimp only [Reg64s.beeuB, ctzClamped] at hB_pos hk h_odd ⊢
    kprologue beeu_mod_inverse_vartime at ".Lbeeu_loop" to ".Lbeeu_shift_loop_X" with s
    have h_nz := val256_pos_or_ne_zero X25 X26 X27 X28 hB_pos
    kfinish beeu_mod_inverse_vartime
  · simp only [hk, ↓reduceIte]
    have h_par := shift256_val256_even_imp_clamped s.regs.X25 s.regs.X26 s.regs.X27 s.regs.X28
    dsimp only [Reg64s.beeuB, ctzClamped] at hB_pos hk ⊢
    kprologue beeu_mod_inverse_vartime at ".Lbeeu_loop" to ".Lbeeu_shift_loop_X" with s
    have h_nz := val256_pos_or_ne_zero X25 X26 X27 X28 hB_pos
    have hk_beq : ((X25.toBitVec.reverse ||| 1#64).clz == 0#64) = false :=
      beq_eq_false_iff_ne.mpr hk
    have h_shift := shift256_val256 X25 X26 X27 X28 hk
    have hk_pos : 0 < (X25.toBitVec.reverse ||| 1#64).clz.toNat := by
      have : (X25.toBitVec.reverse ||| 1#64).clz.toNat ≠ 0 :=
        fun h0 => hk (BitVec.eq_of_toNat_eq h0)
      omega
    kfinish beeu_mod_inverse_vartime [ctzClamped, shift256Word, shift256TopWord]

block_spec beeu_shift_A_header_correct beeu_mod_inverse_vartime s
  from ".Lbeeu_shift_A_Y"
  (writes := [beeuA, X13, X14, X15, X19, X20])
  (post := fun st =>
    let k := ctzClamped s.regs.X21
    st.data.dmem = s.dmem ∧
    if k = 0#64 then
      st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_update_B_X_or_A_Y" ∧
      st.data.regs.beeuA = s.regs.beeuA ∧
      s.regs.beeuA % 2 = 1
    else
      st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_shift_loop_Y" ∧
      st.data.regs.X13.toNat = k.toNat ∧
      0 < k.toNat ∧
      st.data.regs.X14 = 0 ∧
      ((2 ^ k.toNat : Nat) : Int) * st.data.regs.beeuA = s.regs.beeuA ∧
      (st.data.regs.beeuA % 2 = 0 → k = 63#64)) := by
  intro _
  by_cases hk : ctzClamped s.regs.X21 = 0#64
  · simp only [hk, ↓reduceIte]
    have h_odd := val256_odd_of_ctzClamped_eq_zero s.regs.X21 s.regs.X22 s.regs.X23 s.regs.X24 hk
    dsimp only [Reg64s.beeuA, ctzClamped] at hk h_odd ⊢
    kprologue beeu_mod_inverse_vartime at ".Lbeeu_shift_A_Y" to ".Lbeeu_shift_loop_Y" with s
    kfinish beeu_mod_inverse_vartime
  · simp only [hk, ↓reduceIte]
    have h_par := shift256_val256_even_imp_clamped s.regs.X21 s.regs.X22 s.regs.X23 s.regs.X24
    dsimp only [Reg64s.beeuA, ctzClamped] at hk ⊢
    kprologue beeu_mod_inverse_vartime at ".Lbeeu_shift_A_Y" to ".Lbeeu_shift_loop_Y" with s
    have hk_beq : ((X21.toBitVec.reverse ||| 1#64).clz == 0#64) = false :=
      beq_eq_false_iff_ne.mpr hk
    have h_shift := shift256_val256 X21 X22 X23 X24 hk
    have hk_pos : 0 < (X21.toBitVec.reverse ||| 1#64).clz.toNat := by
      have : (X21.toBitVec.reverse ||| 1#64).clz.toNat ≠ 0 :=
        fun h0 => hk (BitVec.eq_of_toNat_eq h0)
      omega
    kfinish beeu_mod_inverse_vartime [ctzClamped, shift256Word, shift256TopWord]

/-- Full verification of the `B`/`X` shift phase (`.Lbeeu_loop` to `.Lbeeu_shift_A_Y` when `B > 0`):
    shifts `B` right by `k = ctzClamped(b0)` bits and divides `X` by `2^k` modulo `N`. -/
block_spec beeu_shift_B_X_correct beeu_mod_inverse_vartime s (a : Int)
  from ".Lbeeu_loop" to ".Lbeeu_shift_A_Y"
  (preserves := [SP, X29, beeuN, beeuA, beeuY])
  (pre :=
    0 < s.regs.beeuB ∧
    s.regs.beeuN % 2 = 1 ∧
    s.regs.beeuX < 256 ^ 40 / 2 ∧
    (a * s.regs.beeuX - s.regs.beeuB) % s.regs.beeuN = 0)
  (post := fun st =>
    st.data.dmem = s.dmem ∧
    0 < st.data.regs.beeuB ∧
    st.data.regs.beeuB ≤ s.regs.beeuB ∧
    st.data.regs.beeuX < 256 ^ 40 / 2 ∧
    (a * st.data.regs.beeuX - st.data.regs.beeuB) % s.regs.beeuN = 0 ∧
    ∃ k : Nat, k ≤ 63 ∧
      ((2 ^ k : Nat) : Int) * st.data.regs.beeuB = s.regs.beeuB ∧
      ((2 ^ k : Nat) : Int) * st.data.regs.beeuX ≤
        s.regs.beeuX + (((2 ^ k : Nat) : Int) - 1) * s.regs.beeuN ∧
      (s.regs.beeuB % 2 = 0 → 1 ≤ k) ∧
      (st.data.regs.beeuB % 2 = 0 → k = 63)) := by
  rintro ⟨hB_pos, hN_odd, hX_lt, h_inv⟩
  kcall beeu_shift_B_header_correct s hB_pos with mid ⟨h_fr, h_dmem, h_branch⟩
  kframe_eqs h_fr
  by_cases hk : ctzClamped s.regs.X25 = 0#64
  · simp only [hk, ↓reduceIte] at h_branch
    rcases h_branch with ⟨h_pc, h_B, h_odd⟩
    apply Eventually.done
    dsimp only
    refine ⟨h_pc, by kframe, h_dmem, h_B.symm ▸ hB_pos, by omega, h_fr_beeuX.symm ▸ hX_lt,
      by rw [h_fr_beeuX, h_B]; exact h_inv,
      0, by omega, by rw [h_B]; simp, by rw [h_fr_beeuX]; simp, by intro h; omega,
      by rw [h_B]; intro h; omega⟩
  · simp only [hk, ↓reduceIte] at h_branch
    rcases h_branch with ⟨h_pc, h_x13, hk_pos, h_x14, h_B_shift, h_par⟩
    have h_N_lt : s.regs.beeuN < 256 ^ 32 := val256_lt _ _ _ _
    have h_xn_lt : mid.regs.beeuX + mid.regs.beeuN < 256 ^ 40 := by
      rw [h_fr_beeuX, h_fr_beeuN]; omega
    subst h_pc
    kcall beeu_shift_loop_X_correct mid ⟨h_x13 ▸ hk_pos, h_x14, h_fr_beeuN.symm ▸ hN_odd, h_xn_lt⟩
      with fin ⟨h_fin_fr, h_fin_dmem, h_fin_X_mod, h_fin_X_lt, h_fin_X_bnd⟩
    kframe_eqs h_fin_fr
    apply Eventually.done
    dsimp only
    have hB_nonneg : 0 ≤ fin.regs.beeuB := val256_nonneg _ _ _ _
    have ⟨hB'_pos, hB'_le⟩ := pos_and_le_of_pow2_mul
      (ctzClamped s.regs.X25).toNat s.regs.beeuB fin.regs.beeuB
      hB_pos hB_nonneg (h_fin_fr_beeuB.symm ▸ h_B_shift)
    have hk63 : (ctzClamped s.regs.X25).toNat ≤ 63 :=
      BitVec.le_def.mp (BitVec.clz_reverse_or_one_le_63 s.regs.X25.toBitVec)
    rw [h_x13, h_fr_beeuN, h_fr_beeuX] at h_fin_X_mod h_fin_X_bnd
    refine ⟨rfl, by kframe, h_fin_dmem.trans h_dmem,
      hB'_pos, hB'_le, h_fin_X_lt, ?_, (ctzClamped s.regs.X25).toNat, hk63,
      h_fin_fr_beeuB.symm ▸ h_B_shift, h_fin_X_bnd, fun _ => hk_pos, ?_⟩
    · exact shift_B_X_mod_inv (ctzClamped s.regs.X25).toNat a
        s.regs.beeuB fin.regs.beeuB s.regs.beeuX fin.regs.beeuX s.regs.beeuN
        hN_odd (h_fin_fr_beeuB.symm ▸ h_B_shift) h_fin_X_mod h_inv
    · intro h_even
      rw [h_fin_fr_beeuB] at h_even
      exact congrArg BitVec.toNat (h_par h_even)

/-- Full verification of the `A`/`Y` shift phase (`.Lbeeu_shift_A_Y` to `.Lbeeu_update_B_X_or_A_Y`):
    shifts `A` right by `k = ctzClamped(a0)` bits and divides `Y` by `2^k` modulo `N`. -/
block_spec beeu_shift_A_Y_correct beeu_mod_inverse_vartime s (a : Int)
  from ".Lbeeu_shift_A_Y" to ".Lbeeu_update_B_X_or_A_Y"
  (preserves := [SP, X29, beeuN, beeuB, beeuX])
  (pre :=
    0 < s.regs.beeuA ∧
    s.regs.beeuN % 2 = 1 ∧
    s.regs.beeuY < 256 ^ 40 / 2 ∧
    (a * s.regs.beeuY + s.regs.beeuA) % s.regs.beeuN = 0)
  (post := fun st =>
    st.data.dmem = s.dmem ∧
    0 < st.data.regs.beeuA ∧
    st.data.regs.beeuA ≤ s.regs.beeuA ∧
    st.data.regs.beeuY < 256 ^ 40 / 2 ∧
    (a * st.data.regs.beeuY + st.data.regs.beeuA) % s.regs.beeuN = 0 ∧
    ∃ k : Nat, k ≤ 63 ∧
      ((2 ^ k : Nat) : Int) * st.data.regs.beeuA = s.regs.beeuA ∧
      ((2 ^ k : Nat) : Int) * st.data.regs.beeuY ≤
        s.regs.beeuY + (((2 ^ k : Nat) : Int) - 1) * s.regs.beeuN ∧
      (s.regs.beeuA % 2 = 0 → 1 ≤ k) ∧
      (st.data.regs.beeuA % 2 = 0 → k = 63)) := by
  rintro ⟨hA_pos, hN_odd, hY_lt, h_inv⟩
  kcall beeu_shift_A_header_correct s trivial with mid ⟨h_fr, h_dmem, h_branch⟩
  kframe_eqs h_fr
  by_cases hk : ctzClamped s.regs.X21 = 0#64
  · simp only [hk, ↓reduceIte] at h_branch
    rcases h_branch with ⟨h_pc, h_A, h_odd⟩
    apply Eventually.done
    dsimp only
    refine ⟨h_pc, by kframe, h_dmem, h_A.symm ▸ hA_pos, by omega, h_fr_beeuY.symm ▸ hY_lt,
      by rw [h_fr_beeuY, h_A]; exact h_inv,
      0, by omega, by rw [h_A]; simp, by rw [h_fr_beeuY]; simp, by intro h; omega,
      by rw [h_A]; intro h; omega⟩
  · simp only [hk, ↓reduceIte] at h_branch
    rcases h_branch with ⟨h_pc, h_x13, hk_pos, h_x14, h_A_shift, h_par⟩
    have h_N_lt : s.regs.beeuN < 256 ^ 32 := val256_lt _ _ _ _
    have h_yn_lt : mid.regs.beeuY + mid.regs.beeuN < 256 ^ 40 := by
      rw [h_fr_beeuY, h_fr_beeuN]; omega
    subst h_pc
    kcall beeu_shift_loop_Y_correct mid ⟨h_x13 ▸ hk_pos, h_x14, h_fr_beeuN.symm ▸ hN_odd, h_yn_lt⟩
      with fin ⟨h_fin_fr, h_fin_dmem, h_fin_Y_mod, h_fin_Y_lt, h_fin_Y_bnd⟩
    kframe_eqs h_fin_fr
    apply Eventually.done
    dsimp only
    have hA_nonneg : 0 ≤ fin.regs.beeuA := val256_nonneg _ _ _ _
    have ⟨hA'_pos, hA'_le⟩ := pos_and_le_of_pow2_mul
      (ctzClamped s.regs.X21).toNat s.regs.beeuA fin.regs.beeuA
      hA_pos hA_nonneg (h_fin_fr_beeuA.symm ▸ h_A_shift)
    have hk63 : (ctzClamped s.regs.X21).toNat ≤ 63 :=
      BitVec.le_def.mp (BitVec.clz_reverse_or_one_le_63 s.regs.X21.toBitVec)
    rw [h_x13, h_fr_beeuN, h_fr_beeuY] at h_fin_Y_mod h_fin_Y_bnd
    refine ⟨rfl, by kframe, h_fin_dmem.trans h_dmem,
      hA'_pos, hA'_le, h_fin_Y_lt, ?_, (ctzClamped s.regs.X21).toNat, hk63,
      h_fin_fr_beeuA.symm ▸ h_A_shift, h_fin_Y_bnd, fun _ => hk_pos, ?_⟩
    · exact shift_A_Y_mod_inv (ctzClamped s.regs.X21).toNat a
        s.regs.beeuA fin.regs.beeuA s.regs.beeuY fin.regs.beeuY s.regs.beeuN
        hN_odd (h_fin_fr_beeuA.symm ▸ h_A_shift) h_fin_Y_mod h_inv
    · intro h_even
      rw [h_fin_fr_beeuA] at h_even
      exact congrArg BitVec.toNat (h_par h_even)

/-! ## Loop Exit, Update Step, and Outer Loop Block Specifications -/

block_spec beeu_loop_exit_when_B_zero beeu_mod_inverse_vartime s₀
  from ".Lbeeu_loop" to ".Lbeeu_loop_end"
  (writes := [X14, X15])
  (pre := s₀.regs.beeuB = 0)
  (post := fun st => st.data.dmem = s₀.dmem) := by
  intro h_B_zero
  have ⟨h25, h26, h27, h28⟩ := val256_eq_zero_limbs
    s₀.regs.X25 s₀.regs.X26 s₀.regs.X27 s₀.regs.X28 h_B_zero
  kprologue beeu_mod_inverse_vartime at ".Lbeeu_loop" to ".Lbeeu_shift_A_Y" with s₀
  kfinish beeu_mod_inverse_vartime

block_spec beeu_update_step_correct beeu_mod_inverse_vartime s₀
  from ".Lbeeu_update_B_X_or_A_Y" to ".Lbeeu_loop"
  (preserves := [SP, X29, beeuN])
  (pre := s₀.regs.beeuX + s₀.regs.beeuY < 256 ^ 40)
  (post := fun st =>
    st.data.dmem = s₀.dmem ∧
    if s₀.regs.beeuB ≥ s₀.regs.beeuA then
      st.data.regs.beeuB = s₀.regs.beeuB - s₀.regs.beeuA ∧
      st.data.regs.beeuA = s₀.regs.beeuA ∧
      st.data.regs.beeuX = s₀.regs.beeuX + s₀.regs.beeuY ∧
      st.data.regs.beeuY = s₀.regs.beeuY
    else
      st.data.regs.beeuB = s₀.regs.beeuB ∧
      st.data.regs.beeuA = s₀.regs.beeuA - s₀.regs.beeuB ∧
      st.data.regs.beeuX = s₀.regs.beeuX ∧
      st.data.regs.beeuY = s₀.regs.beeuY + s₀.regs.beeuX) := by
  intro h_xy_bound
  kprologue beeu_mod_inverse_vartime at ".Lbeeu_update_B_X_or_A_Y" to ".Lbeeu_B_greater_than_A" with s₀
  by_cases h_ge : val256 X25 X26 X27 X28 ≥ val256 X21 X22 X23 X24
  · have h_carry := sub256_carry_of_ge X25 X26 X27 X28 X21 X22 X23 X24 h_ge
    have hB' := sub256_val_of_ge X25 X26 X27 X28 X21 X22 X23 X24 h_ge
    have hX' := add320_val_of_lt X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 h_xy_bound
    kstep
    kprologue beeu_mod_inverse_vartime at ".Lbeeu_B_greater_than_A" to ".Lbeeu_loop_end"
    kfinish beeu_mod_inverse_vartime [Reg64s.beeuB, Reg64s.beeuA, Reg64s.beeuN, Reg64s.beeuX,
      Reg64s.beeuY, h_ge]
  · have h_lt : val256 X25 X26 X27 X28 < val256 X21 X22 X23 X24 := Int.lt_of_not_ge h_ge
    have h_le : val256 X21 X22 X23 X24 ≥ val256 X25 X26 X27 X28 := Int.le_of_lt h_lt
    have h_carry := sub256_carry_of_lt X25 X26 X27 X28 X21 X22 X23 X24 h_lt
    have h_yx_bound : val320 X8 X9 X10 X11 X12 + val320 X3 X4 X5 X6 X7 < 256 ^ 40 := by
      dsimp only [Reg64s.beeuX, Reg64s.beeuY] at h_xy_bound; omega
    have hA' := sub256_val_of_ge X21 X22 X23 X24 X25 X26 X27 X28 h_le
    have hY' := add320_val_of_lt X8 X9 X10 X11 X12 X3 X4 X5 X6 X7 h_yx_bound
    kfinish beeu_mod_inverse_vartime [Reg64s.beeuB, Reg64s.beeuA, Reg64s.beeuN, Reg64s.beeuX,
      Reg64s.beeuY, h_ge]

/-- One full iteration of `.Lbeeu_loop` when `0 < B`:
    executes `beeu_shift_B_X`, `beeu_shift_A_Y`, and `.Lbeeu_update_B_X_or_A_Y`,
    returning to `.Lbeeu_loop` with strictly smaller `(B + A).toNat` and re-establishing
    the loop invariant `BeeuInv` for updated ghost counters `σ' τ'`. -/
block_spec beeu_loop_body_correct beeu_mod_inverse_vartime s (a : Int) (σ τ : Nat)
  from ".Lbeeu_loop" to ".Lbeeu_loop"
  (preserves := [SP, X29, beeuN])
  (pre :=
    0 < s.regs.beeuB ∧
    BeeuInv a s.regs.beeuN σ τ s.regs.beeuB s.regs.beeuA s.regs.beeuX s.regs.beeuY)
  (post := fun st =>
    st.data.dmem = s.dmem ∧
    st.data.regs.beeuA ≤ s.regs.beeuA ∧
    (st.data.regs.beeuB + st.data.regs.beeuA).toNat <
      (s.regs.beeuB + s.regs.beeuA).toNat ∧
    ∃ σ' τ' : Nat,
      BeeuInv a s.regs.beeuN σ' τ' st.data.regs.beeuB st.data.regs.beeuA
        st.data.regs.beeuX st.data.regs.beeuY) := by
  rintro ⟨hB_pos, hI⟩
  have hN_lt : s.regs.beeuN < 256 ^ 32 := val256_lt _ _ _ _
  have hN_pos : 0 < s.regs.beeuN := by have := hI.A_pos; have := hI.A_le; omega
  have hN0 : 0 ≤ s.regs.beeuN := Int.le_of_lt hN_pos
  have hM0 : 0 ≤ beeuBound σ τ := Int.le_of_lt (beeuBound_pos σ τ)
  obtain ⟨hX_lt, hY_lt, hM_512⟩ := hI.bounds hB_pos hN_lt
  -- Phase 1: shift B and X.
  kcall beeu_shift_B_X_correct s a ⟨hB_pos, hI.N_odd, hX_lt, hI.X_inv⟩
    with st1 ⟨h1_fr, h1_dmem, h1_B_pos, h1_B_le, h1_X_lt, h1_X_inv,
      k₁, hk₁_le, h1_B_shift, h1_X_bnd, h1_k₁_pos, h1_clamp⟩
  kframe_eqs h1_fr
  -- Phase 2: shift A and Y.
  kcall beeu_shift_A_Y_correct st1 a
      ⟨h1_fr_beeuA.symm ▸ hI.A_pos, h1_fr_beeuN.symm ▸ hI.N_odd, h1_fr_beeuY.symm ▸ hY_lt, by
        rw [h1_fr_beeuY, h1_fr_beeuA, h1_fr_beeuN]; exact hI.Y_inv⟩
    with st2 ⟨h2_fr, h2_dmem, h2_A_pos, h2_A_le, h2_Y_lt, h2_Y_inv,
      k₂, hk₂_le, h2_A_shift, h2_Y_bnd, h2_k₂_pos, h2_clamp⟩
  kframe_eqs h2_fr
  have h2_B := h2_fr_beeuB
  have h2_X := h2_fr_beeuX
  rw [h1_fr_beeuA] at h2_A_shift h2_k₂_pos h2_A_le
  rw [h1_fr_beeuY, h1_fr_beeuN] at h2_Y_bnd
  rw [h1_fr_beeuN] at h2_Y_inv
  -- Quantitative bounds after the shift phases, relative to the loop-top multiplier `M`.
  have hX₂ : st2.regs.beeuX < s.regs.beeuN * (beeuBound σ τ + k₁) := by
    rw [h2_X]
    exact shift_phase_bound _ _ _ _ _ k₁ hN0 hM0 hI.X_lt hI.X_lt_odd h1_k₁_pos h1_X_bnd
  have hY₂ : st2.regs.beeuY < s.regs.beeuN * (beeuBound σ τ + k₂) :=
    shift_phase_bound _ _ _ _ _ k₂ hN0 hM0 hI.Y_lt hI.Y_lt_odd h2_k₂_pos h2_Y_bnd
  -- Phase 3: the update step.
  have h_xy_lt : st2.regs.beeuX + st2.regs.beeuY < 256 ^ 40 := by omega
  kcall beeu_update_step_correct st2 h_xy_lt with fin ⟨h3_fr, h3_dmem, h3_branch⟩
  apply Eventually.done
  dsimp only
  have h2_B_pos : 0 < st2.regs.beeuB := h2_B.symm ▸ h1_B_pos
  have h2_B_le : st2.regs.beeuB ≤ s.regs.beeuB := h2_B.symm ▸ h1_B_le
  have h2_X_inv : (a * st2.regs.beeuX - st2.regs.beeuB) % s.regs.beeuN = 0 := by
    rw [h2_X, h2_B]; exact h1_X_inv
  have h2_X_bnd : ((2 ^ k₁ : Nat) : Int) * st2.regs.beeuX ≤
      s.regs.beeuX + (((2 ^ k₁ : Nat) : Int) - 1) * s.regs.beeuN := h2_X ▸ h1_X_bnd
  have hI_B_le := hI.B_le
  have hI_A_le := hI.A_le
  have hI_B_nonneg := hI.B_nonneg
  have hI_A_pos := hI.A_pos
  -- Euclid's invariant survives the shifts because `gcd A B ∣ N` is odd.
  have hg_odd : (Int.gcd s.regs.beeuA s.regs.beeuB : Int) % 2 = 1 := by
    rw [hI.gcd_eq]
    exact odd_of_dvd_odd _ _ hI.N_odd (Int.gcd_dvd_right a s.regs.beeuN)
  have hg1 : Int.gcd s.regs.beeuA st2.regs.beeuB = Int.gcd s.regs.beeuA s.regs.beeuB :=
    Int.gcd_of_two_pow_mul_odd _ _ _ k₁ (by rw [h2_B]; exact h1_B_shift) hg_odd
  have hg_odd' : (Int.gcd st2.regs.beeuB s.regs.beeuA : Int) % 2 = 1 := by
    rw [Int.gcd_comm, hg1]; exact hg_odd
  have hg2 : Int.gcd st2.regs.beeuA st2.regs.beeuB = Int.gcd a s.regs.beeuN := by
    rw [Int.gcd_comm, Int.gcd_of_two_pow_mul_odd _ _ _ k₂ h2_A_shift hg_odd', Int.gcd_comm, hg1,
      hI.gcd_eq]
  have hM_eq := beeuBound_add σ τ k₁ k₂
  have h_parity_clamp : (st2.regs.beeuB - st2.regs.beeuA) % 2 = 1 ∨
      (st2.regs.beeuA - st2.regs.beeuB) % 2 = 1 → k₁ = 63 ∨ k₂ = 63 := by
    intro h
    have hBe : st2.regs.beeuB % 2 = 0 ∨ st2.regs.beeuA % 2 = 0 := by omega
    rcases hBe with hB0 | hA0
    · exact Or.inl (h1_clamp (h2_B ▸ hB0))
    · exact Or.inr (h2_clamp hA0)
  -- Shifted-multiple facts for B and A.
  have hpow_σ : ((2 ^ (σ + k₁) : Nat) : Int) = ((2 ^ σ : Nat) : Int) * ((2 ^ k₁ : Nat) : Int) := by
    rw [Nat.pow_add, Int.natCast_mul]
  have hpow_τ : ((2 ^ (τ + k₂) : Nat) : Int) = ((2 ^ τ : Nat) : Int) * ((2 ^ k₂ : Nat) : Int) := by
    rw [Nat.pow_add, Int.natCast_mul]
  have h2σ : (0 : Int) ≤ ((2 ^ σ : Nat) : Int) := by exact_mod_cast Nat.zero_le _
  have h2τ : (0 : Int) ≤ ((2 ^ τ : Nat) : Int) := by exact_mod_cast Nat.zero_le _
  have h2k₁ : (0 : Int) ≤ ((2 ^ k₁ : Nat) : Int) := by exact_mod_cast Nat.zero_le _
  have h2k₂ : (0 : Int) ≤ ((2 ^ k₂ : Nat) : Int) := by exact_mod_cast Nat.zero_le _
  have hB_shifted' : ∀ B₃ : Int, B₃ ≤ st2.regs.beeuB →
      ((2 ^ (σ + k₁) : Nat) : Int) * B₃ ≤ s.regs.beeuN := by
    intro B₃ hB₃
    calc ((2 ^ (σ + k₁) : Nat) : Int) * B₃
        = ((2 ^ σ : Nat) : Int) * (((2 ^ k₁ : Nat) : Int) * B₃) := by rw [hpow_σ, Int.mul_assoc]
      _ ≤ ((2 ^ σ : Nat) : Int) * (((2 ^ k₁ : Nat) : Int) * st2.regs.beeuB) :=
          Int.mul_le_mul_of_nonneg_left (Int.mul_le_mul_of_nonneg_left hB₃ h2k₁) h2σ
      _ = ((2 ^ σ : Nat) : Int) * s.regs.beeuB := by rw [h2_B, h1_B_shift]
      _ ≤ s.regs.beeuN := hI.B_shifted
  have hA_shifted' : ∀ A₃ : Int, A₃ ≤ st2.regs.beeuA →
      ((2 ^ (τ + k₂) : Nat) : Int) * A₃ ≤ s.regs.beeuN := by
    intro A₃ hA₃
    calc ((2 ^ (τ + k₂) : Nat) : Int) * A₃
        = ((2 ^ τ : Nat) : Int) * (((2 ^ k₂ : Nat) : Int) * A₃) := by rw [hpow_τ, Int.mul_assoc]
      _ ≤ ((2 ^ τ : Nat) : Int) * (((2 ^ k₂ : Nat) : Int) * st2.regs.beeuA) :=
          Int.mul_le_mul_of_nonneg_left (Int.mul_le_mul_of_nonneg_left hA₃ h2k₂) h2τ
      _ = ((2 ^ τ : Nat) : Int) * s.regs.beeuA := by rw [h2_A_shift]
      _ ≤ s.regs.beeuN := hI.A_shifted
  have hM'0 : 0 ≤ s.regs.beeuN * beeuBound (σ + k₁) (τ + k₂) :=
    Int.mul_nonneg hN0 (Int.le_of_lt (beeuBound_pos _ _))
  refine ⟨rfl, by kframe, h3_dmem.trans (h2_dmem.trans h1_dmem), ?_, ?_,
    σ + k₁, τ + k₂, ?_⟩
  all_goals by_cases h_ge : st2.regs.beeuB ≥ st2.regs.beeuA
  all_goals simp only [h_ge, ↓reduceIte] at h3_branch
  all_goals rcases h3_branch with ⟨hB', hA', hX', hY'⟩
  · omega
  · omega
  · omega
  · omega
  · -- B ≥ A: B := B − A, X := X + Y
    refine ⟨hI.N_odd, ?_, by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hA', hB', Int.gcd_sub_self_right]; exact hg2
    · have h_lin : a * fin.regs.beeuX - fin.regs.beeuB =
          (a * st2.regs.beeuX - st2.regs.beeuB) + (a * st2.regs.beeuY + st2.regs.beeuA) := by
        rw [hX', hB']; grind
      rw [h_lin, Int.add_emod, h2_X_inv, h2_Y_inv]; simp
    · rw [hY', hA']; exact h2_Y_inv
    · exact hB_shifted' _ (by omega)
    · exact hA_shifted' _ (by omega)
    · rw [hX']
      exact update_bound_even _ _ _ _ _ k₁ k₂ hN0 hX₂ hY₂ (by omega)
    · intro h_odd
      rw [hX']
      exact update_bound_clamped _ _ _ _ _ _ _ k₁ k₂ hN0 hM_512 hI.X_lt hI.Y_lt hX₂ hY₂
        h2_X_bnd h2_Y_bnd (h_parity_clamp (Or.inl (hB' ▸ h_odd))) (by omega)
    · rw [hY']
      have := bound_mono_right _ _ _ _ hN0 hY₂
        (by omega : beeuBound σ τ + k₂ ≤ beeuBound (σ + k₁) (τ + k₂))
      omega
    · intro _
      rw [hY']
      exact bound_mono_right _ _ _ _ hN0 hY₂ (by omega)
  · -- B < A: A := A − B, Y := Y + X
    refine ⟨hI.N_odd, ?_, by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hA', hB', Int.gcd_sub_self_left]; exact hg2
    · rw [hX', hB']; exact h2_X_inv
    · have h_lin : a * fin.regs.beeuY + fin.regs.beeuA =
          (a * st2.regs.beeuY + st2.regs.beeuA) + (a * st2.regs.beeuX - st2.regs.beeuB) := by
        rw [hY', hA']; grind
      rw [h_lin, Int.add_emod, h2_Y_inv, h2_X_inv]; simp
    · exact hB_shifted' _ (by omega)
    · exact hA_shifted' _ (by omega)
    · rw [hX']
      have := bound_mono_right _ _ _ _ hN0 hX₂
        (by omega : beeuBound σ τ + k₁ ≤ beeuBound (σ + k₁) (τ + k₂))
      omega
    · intro _
      rw [hX']
      exact bound_mono_right _ _ _ _ hN0 hX₂ (by omega)
    · rw [hY']
      have := update_bound_even st2.regs.beeuY st2.regs.beeuX s.regs.beeuN (beeuBound σ τ)
        (beeuBound (σ + k₁) (τ + k₂)) k₂ k₁ hN0 hY₂ hX₂ (by omega)
      omega
    · intro h_odd
      rw [hY']
      have := update_bound_clamped s.regs.beeuX st2.regs.beeuX s.regs.beeuY st2.regs.beeuY
        s.regs.beeuN (beeuBound σ τ) (beeuBound (σ + k₁) (τ + k₂)) k₁ k₂ hN0 hM_512
        hI.X_lt hI.Y_lt hX₂ hY₂ h2_X_bnd h2_Y_bnd (h_parity_clamp (Or.inr (hA' ▸ h_odd))) (by omega)
      omega

/-- Full verification of the outer binary extended Euclidean loop (`.Lbeeu_loop` to `.Lbeeu_loop_end`):
    terminates by well-founded induction on `(B + A).toNat`, carrying the ghost invariant `BeeuInv`
    (which keeps `X, Y < 2^319` in every reachable state), exiting with `B = 0`, `0 < A ≤ A₀`,
    `(a * Y + A) % N = 0`, and `A = 1 ↔ gcd a N = 1`. -/
block_spec beeu_loop_correct beeu_mod_inverse_vartime s (a : Int)
  from ".Lbeeu_loop" to ".Lbeeu_loop_end"
  (preserves := [SP, X29, beeuN])
  (pre := BeeuInv a s.regs.beeuN 0 0 s.regs.beeuB s.regs.beeuA s.regs.beeuX s.regs.beeuY)
  (post := fun st =>
    st.data.dmem = s.dmem ∧
    0 < st.data.regs.beeuA ∧
    st.data.regs.beeuA ≤ s.regs.beeuA ∧
    (a * st.data.regs.beeuY + st.data.regs.beeuA) % s.regs.beeuN = 0 ∧
    (st.data.regs.beeuA = 1 ↔ Int.gcd a s.regs.beeuN = 1)) := by
  intro hI
  kloop at ".Lbeeu_loop" (preserves := [SP, X29, beeuN])
    (inv := fun v (σ, τ) st =>
      st.data.dmem = s.dmem ∧
      st.data.regs.beeuA ≤ s.regs.beeuA ∧
      (st.data.regs.beeuB + st.data.regs.beeuA).toNat = v ∧
      BeeuInv a s.regs.beeuN σ τ st.data.regs.beeuB st.data.regs.beeuA
        st.data.regs.beeuX st.data.regs.beeuY)
    (measure := (s.regs.beeuB + s.regs.beeuA).toNat)
    (ghost := ((0 : Nat), (0 : Nat)))
    (state := st_data)
    with v ⟨σ, τ⟩ ⟨hst_dmem, hst_A_le, hst_v, hst_I⟩
  · exact ⟨rfl, Int.le_refl _, rfl, hI⟩
  · by_cases hB0 : st_data.regs.beeuB = 0
    · kcall beeu_loop_exit_when_B_zero st_data hB0 with fin ⟨h_fr', h_dmem'⟩
      kframe_eqs h_fr'
      kloop_exit
      refine ⟨rfl, by kframe, h_dmem'.trans hst_dmem, h_fr'_beeuA.symm ▸ hst_I.A_pos,
        h_fr'_beeuA.symm ▸ hst_A_le, ?_, ?_⟩
      · rw [h_fr'_beeuY, h_fr'_beeuA]
        exact hst_I.Y_inv
      · -- `B = 0`, so `A = gcd A 0 = gcd a N`.
        have hg := hst_I.gcd_eq
        rw [hB0, Int.gcd_zero] at hg
        have hA_pos := hst_I.A_pos
        rw [h_fr'_beeuA]
        constructor
        · intro h; rw [← hg]; omega
        · intro h; rw [← hg] at h; omega
    · have hst_B_pos : 0 < st_data.regs.beeuB := by have := hst_I.B_nonneg; omega
      have hst_I' : BeeuInv a st_data.regs.beeuN σ τ st_data.regs.beeuB st_data.regs.beeuA
          st_data.regs.beeuX st_data.regs.beeuY := by
        rw [h_fr_beeuN]; exact hst_I
      kcall beeu_loop_body_correct st_data a σ τ ⟨hst_B_pos, hst_I'⟩
        with mid ⟨h_fr', h_dmem', h_A_le', h_lt', σ', τ', hI'⟩
      kloop_next (mid.regs.beeuB + mid.regs.beeuA).toNat (σ', τ')
      refine ⟨h_dmem'.trans hst_dmem, Int.le_trans h_A_le' hst_A_le, rfl, ?_⟩
      rw [← h_fr_beeuN]
      exact hI'

/-! ## Post-Loop Reduction and Epilogue Block Specifications -/

block_spec beeu_epilogue_err_correct beeu_mod_inverse_vartime s
  (r₀ : Reg64s) (R : DataMem → Prop)
  from ".Lbeeu_err"
  (exit := Int64.ofInt r₀.X30.toBitVec.toInt)
  (pre :=
    let sp' := r₀.SP.toBitVec + 18446744073709551504#64
    r₀.SP.toBitVec % 16#64 = 0#64 ∧
    s.regs.X29 = UInt64.ofBitVec sp' ∧
    (s.dmem =⋆ BeeuStackFrame r₀ sp' ⋆ R))
  (post := fun st =>
    let sp' := r₀.SP.toBitVec + 18446744073709551504#64
    st.data.regs.X0 = 0 ∧
    st.data.regs.SP = r₀.SP ∧
    st.data.regs.X30 = r₀.X30 ∧
    st.data.regs.CalleeSavedEq r₀ ∧
    (st.data.dmem =⋆ BeeuStackFrame r₀ sp' ⋆ R)) := by
  rintro ⟨h_sp_align, h_x29, h_mem⟩
  dsimp only [BeeuStackFrame, BeeuSavedRegs] at h_mem ⊢
  kprologue beeu_mod_inverse_vartime at ".Lbeeu_err" with s
  subst h_x29
  kfinish beeu_mod_inverse_vartime [BitVec.ofInt_ofBytes_toBytes_64, Reg64s.CalleeSavedEq]

block_spec beeu_reduction_and_store_correct beeu_mod_inverse_vartime s
  (sp' out_p : BitVec 64) (o0 o1 o2 o3 : UInt64) (R : DataMem → Prop)
  from ".Lbeeu_reduction_loop" to ".Lbeeu_finish"
  (pre :=
    sp' % 16#64 = 0#64 ∧
    s.regs.SP = UInt64.ofBitVec sp' ∧
    s.regs.X12 = 0 ∧
    s.regs.X14 = 0 ∧
    s.regs.beeuY256 < s.regs.beeuN ∧
    (s.dmem =⋆
      (Int.toBytes 8 out_p.toInt) @ (sp' + 96#64) ⋆
      Words256At o0 o1 o2 o3 out_p ⋆
      R))
  (post := fun st =>
    st.data.regs.X0 = 1 ∧
    st.data.regs.SP = UInt64.ofBitVec sp' ∧
    st.data.regs.X29 = s.regs.X29 ∧
    ∃ w0 w1 w2 w3 : UInt64,
      val256 w0 w1 w2 w3 = s.regs.beeuN - s.regs.beeuY256 ∧
      (st.data.dmem =⋆
        (Int.toBytes 8 out_p.toInt) @ (sp' + 96#64) ⋆
        Words256At w0 w1 w2 w3 out_p ⋆
        R)) := by
  rintro ⟨h_sp_align, h_sp, h12, h14, h_lt, h_mem⟩
  dsimp only [Words256At, Reg64s.beeuY256, Reg64s.beeuN] at h_lt h_mem ⊢
  kprologue beeu_mod_inverse_vartime at ".Lbeeu_reduction_loop" to ".Lbeeu_err" with s
  subst h_sp h12 h14
  have h_carry4 := sub256_carry_of_lt X8 X9 X10 X11 X0 X1 X2 X30 h_lt
  have h_le : val256 X0 X1 X2 X30 ≥ val256 X8 X9 X10 X11 := Int.le_of_lt h_lt
  have h_sub := sub256_val_of_ge X0 X1 X2 X30 X8 X9 X10 X11 h_le
  have h_zero_sbc : (StatusFlags.sbcs 0#64 0#64 false).c = false := by decide
  kstep
  apply Eventually.done
  dsimp +zetaDelta only [sub0Carry, sbcCarry, sub0Word, sbcWord] at *
  simp only [h_carry4, h_zero_sbc] at *
  refine ⟨by kaddr beeu_mod_inverse_vartime, rfl, trivial, trivial, _, _, _, _, h_sub, by ecancel⟩

block_spec beeu_finish_correct beeu_mod_inverse_vartime s
  (r₀ : Reg64s) (R : DataMem → Prop)
  from ".Lbeeu_finish"
  (exit := Int64.ofInt r₀.X30.toBitVec.toInt)
  (pre :=
    let sp' := r₀.SP.toBitVec + 18446744073709551504#64
    r₀.SP.toBitVec % 16#64 = 0#64 ∧
    s.regs.X29 = UInt64.ofBitVec sp' ∧
    (s.dmem =⋆ BeeuStackFrame r₀ sp' ⋆ R))
  (post := fun st =>
    let sp' := r₀.SP.toBitVec + 18446744073709551504#64
    st.data.regs.X0 = s.regs.X0 ∧
    st.data.regs.SP = r₀.SP ∧
    st.data.regs.X30 = r₀.X30 ∧
    st.data.regs.CalleeSavedEq r₀ ∧
    (st.data.dmem =⋆ BeeuStackFrame r₀ sp' ⋆ R)) := by
  rintro ⟨h_sp_align, h_x29, h_mem⟩
  dsimp only [BeeuStackFrame, BeeuSavedRegs] at h_mem ⊢
  kprologue beeu_mod_inverse_vartime at ".Lbeeu_finish" with s
  subst h_x29
  kfinish beeu_mod_inverse_vartime [BitVec.ofInt_ofBytes_toBytes_64, Reg64s.CalleeSavedEq]

block_spec beeu_loop_end_correct beeu_mod_inverse_vartime s
  from ".Lbeeu_loop_end"
  (writes := [X14])
  (post := fun st =>
    st.data.dmem = s.dmem ∧
    if s.regs.beeuA = 1 then
      st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_reduction_loop" ∧
      st.data.regs.X14 = 0
    else
      st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_err") := by
  intro _
  by_cases hA : s.regs.beeuA = 1
  · simp only [hA, ↓reduceIte]
    dsimp only [Reg64s.beeuA] at hA
    kprologue beeu_mod_inverse_vartime at ".Lbeeu_loop_end" to ".Lbeeu_reduction_loop" with s
    have ⟨h21, h22, h23, h24⟩ := val256_eq_one_limbs X21 X22 X23 X24 hA
    kfinish beeu_mod_inverse_vartime
  · simp only [hA, ↓reduceIte]
    dsimp only [Reg64s.beeuA] at hA
    kprologue beeu_mod_inverse_vartime at ".Lbeeu_loop_end" to ".Lbeeu_reduction_loop" with s
    have h_nz := val256_ne_one_or_ne_zero X21 X22 X23 X24 hA
    kfinish beeu_mod_inverse_vartime

block_spec beeu_reduction_step_ge_correct beeu_mod_inverse_vartime s
  from ".Lbeeu_reduction_loop" to ".Lbeeu_reduction_loop"
  (writes := [beeuX, beeuY])
  (pre :=
    s.regs.X14 = 0 ∧
    s.regs.beeuY ≥ s.regs.beeuN)
  (post := fun st =>
    st.data.dmem = s.dmem ∧
    st.data.regs.beeuY = s.regs.beeuY - s.regs.beeuN) := by
  rintro ⟨h14, h_ge⟩
  dsimp only [Reg64s.beeuY, Reg64s.beeuN] at h_ge ⊢
  kprologue beeu_mod_inverse_vartime at ".Lbeeu_reduction_loop" to ".Lbeeu_err" with s
  have h0 : (0 : UInt64).toNat = 0 := rfl
  have h_ge320 : val320 X8 X9 X10 X11 X12 ≥ val320 X0 X1 X2 X30 X14 := by
    subst h14
    dsimp only [val320, val256] at h_ge ⊢
    omega
  have h_carry := sub320_carry_of_ge X8 X9 X10 X11 X12 X0 X1 X2 X30 X14 h_ge320
  have h_sub := sub320_val_of_ge X8 X9 X10 X11 X12 X0 X1 X2 X30 X14 h_ge320
  kfinish beeu_mod_inverse_vartime [sub0Carry, sbcCarry, sub0Word, sbcWord, h_carry]
  rw [h_sub]
  subst h14
  dsimp only [val320, val256]
  omega

/-- Full verification of `.Lbeeu_reduction_loop` through `.Lbeeu_finish` to `ret`:
    repeatedly subtracts `N` from `Y` while `Y ≥ N`, then stores `N - (Y % N)` to `out_p`,
    restores callee-saved registers, and returns `1`. -/
block_spec beeu_reduction_to_return_correct beeu_mod_inverse_vartime s
  (r₀ : Reg64s) (o0 o1 o2 o3 : UInt64) (R : DataMem → Prop)
  from ".Lbeeu_reduction_loop"
  (exit := Int64.ofInt r₀.X30.toBitVec.toInt)
  (pre :=
    let sp' := r₀.SP.toBitVec + 18446744073709551504#64
    r₀.SP.toBitVec % 16#64 = 0#64 ∧
    s.regs.SP = UInt64.ofBitVec sp' ∧
    s.regs.X29 = UInt64.ofBitVec sp' ∧
    s.regs.X14 = 0 ∧
    0 < s.regs.beeuN ∧
    (s.dmem =⋆
      BeeuStackFrame r₀ sp' ⋆
      Words256At o0 o1 o2 o3 r₀.X0.toBitVec ⋆
      R))
  (post := fun st =>
    let sp' := r₀.SP.toBitVec + 18446744073709551504#64
    st.data.regs.X0 = 1 ∧
    st.data.regs.SP = r₀.SP ∧
    st.data.regs.X30 = r₀.X30 ∧
    st.data.regs.CalleeSavedEq r₀ ∧
    ∃ w0 w1 w2 w3 : UInt64,
      val256 w0 w1 w2 w3 = s.regs.beeuN - (s.regs.beeuY % s.regs.beeuN) ∧
      (st.data.dmem =⋆
        BeeuStackFrame r₀ sp' ⋆
        Words256At w0 w1 w2 w3 r₀.X0.toBitVec ⋆
        R)) := by
  rintro ⟨h_sp_align, h_sp, h_x29, h_x14, h_n_pos, h_mem⟩
  let sp' := r₀.SP.toBitVec + 18446744073709551504#64
  kloop at ".Lbeeu_reduction_loop" (preserves := [SP, X29, X14, beeuN])
    (inv := fun v st =>
      st.data.dmem = s.dmem ∧
      st.data.regs.beeuY % s.regs.beeuN = s.regs.beeuY % s.regs.beeuN ∧
      st.data.regs.beeuY.toNat = v)
    (measure := s.regs.beeuY.toNat)
    (state := st_data)
    with v _ ⟨hst_dmem, hst_Y_mod, hst_v⟩
  · exact ⟨rfl, rfl, rfl⟩
  · have hst_x14 : st_data.regs.X14 = 0 := h_fr_X14.trans h_x14
    by_cases h_ge : st_data.regs.beeuY ≥ st_data.regs.beeuN
    · kcall beeu_reduction_step_ge_correct st_data ⟨hst_x14, h_ge⟩ with mid ⟨h_fr', h_dmem', h_Y'⟩
      kloop_next mid.regs.beeuY.toNat
      refine ⟨h_dmem'.trans hst_dmem, ?_, rfl⟩
      rw [h_Y', h_fr_beeuN, Int.sub_emod, Int.emod_self, Int.sub_zero, Int.emod_emod, hst_Y_mod]
    · have h_lt : st_data.regs.beeuY < st_data.regs.beeuN := Int.lt_of_not_ge h_ge
      have h_N_lt : st_data.regs.beeuN < 256 ^ 32 := val256_lt _ _ _ _
      have ⟨h_x12, h_y256⟩ := val320_lt_256_pow_32
        st_data.regs.X8 st_data.regs.X9 st_data.regs.X10 st_data.regs.X11 st_data.regs.X12
        (by dsimp only [Reg64s.beeuY] at h_lt; omega)
      have h_y256_lt : st_data.regs.beeuY256 < st_data.regs.beeuN := by
        dsimp only [Reg64s.beeuY256]; rw [h_y256]; exact h_lt
      have h_sp_align' : sp' % 16#64 = 0#64 := by
        dsimp only [sp']; rw [sp_sub_112_mod_16]; exact h_sp_align
      have h_mem_st : (st_data.dmem =⋆
          (Int.toBytes 8 r₀.X0.toBitVec.toInt) @ (sp' + 96#64) ⋆
          Words256At o0 o1 o2 o3 r₀.X0.toBitVec ⋆
          (BeeuSavedRegs r₀ sp' ⋆
           (Int.toBytes 8 r₀.X2.toBitVec.toInt) @ (sp' + 104#64) ⋆ R)) := by
        rw [hst_dmem]
        dsimp only [BeeuStackFrame] at h_mem ⊢
        ecancel
      kcall beeu_reduction_and_store_correct st_data sp' r₀.X0.toBitVec o0 o1 o2 o3 _
          ⟨h_sp_align', h_fr_SP.trans h_sp, h_x12, hst_x14, h_y256_lt, h_mem_st⟩
        with mid_data ⟨h_mid_x0, h_mid_sp, h_mid_x29, w0, w1, w2, w3, h_mid_val, h_mid_mem⟩
      have h_mid_mem' : (mid_data.dmem =⋆
          BeeuStackFrame r₀ sp' ⋆
          (Words256At w0 w1 w2 w3 r₀.X0.toBitVec ⋆ R)) := by
        dsimp +zetaDelta only [BeeuStackFrame] at h_mid_mem ⊢
        ecancel
      kcall beeu_finish_correct mid_data r₀ (Words256At w0 w1 w2 w3 r₀.X0.toBitVec ⋆ R)
          ⟨h_sp_align, h_mid_x29.trans (h_fr_X29.trans h_x29), h_mid_mem'⟩
        with fin ⟨h_fin_x0, h_fin_sp, h_fin_x30, h_fin_cs, h_fin_mem⟩
      kloop_exit
      refine ⟨rfl, h_fin_x0.trans h_mid_x0, h_fin_sp, h_fin_x30, h_fin_cs,
        w0, w1, w2, w3, ?_, by ecancel⟩
      have hY_nonneg : 0 ≤ st_data.regs.beeuY := val320_nonneg _ _ _ _ _
      have hY_mod_eq : st_data.regs.beeuY % s.regs.beeuN = st_data.regs.beeuY :=
        Int.emod_eq_of_lt hY_nonneg (h_fr_beeuN ▸ h_lt)
      dsimp only [Reg64s.beeuY256] at h_mid_val
      rw [h_mid_val, h_y256, h_fr_beeuN, ← hst_Y_mod, hY_mod_eq]

/-- Complete verification from `.Lbeeu_loop_end` to function return:
    if `A = 1`, reduces `Y` modulo `N`, writes `N - (Y % N)` to `out`, and returns `1`;
    if `A ≠ 1`, leaves `out` unchanged and returns `0`. -/
block_spec beeu_loop_end_to_return_correct beeu_mod_inverse_vartime s
  (r₀ : Reg64s) (o0 o1 o2 o3 : UInt64) (R : DataMem → Prop)
  from ".Lbeeu_loop_end"
  (exit := Int64.ofInt r₀.X30.toBitVec.toInt)
  (pre :=
    let sp' := r₀.SP.toBitVec + 18446744073709551504#64
    r₀.SP.toBitVec % 16#64 = 0#64 ∧
    s.regs.SP = UInt64.ofBitVec sp' ∧
    s.regs.X29 = UInt64.ofBitVec sp' ∧
    0 < s.regs.beeuN ∧
    (s.dmem =⋆
      BeeuStackFrame r₀ sp' ⋆
      Words256At o0 o1 o2 o3 r₀.X0.toBitVec ⋆
      R))
  (post := fun st =>
    let sp' := r₀.SP.toBitVec + 18446744073709551504#64
    st.data.regs.SP = r₀.SP ∧
    st.data.regs.X30 = r₀.X30 ∧
    st.data.regs.CalleeSavedEq r₀ ∧
    if s.regs.beeuA = 1 then
      st.data.regs.X0 = 1 ∧
      ∃ w0 w1 w2 w3 : UInt64,
        val256 w0 w1 w2 w3 = s.regs.beeuN - (s.regs.beeuY % s.regs.beeuN) ∧
        (st.data.dmem =⋆
          BeeuStackFrame r₀ sp' ⋆
          Words256At w0 w1 w2 w3 r₀.X0.toBitVec ⋆
          R)
    else
      st.data.regs.X0 = 0 ∧
      (st.data.dmem =⋆
        BeeuStackFrame r₀ sp' ⋆
        Words256At o0 o1 o2 o3 r₀.X0.toBitVec ⋆
        R)) := by
  rintro ⟨h_sp_align, h_sp, h_x29, h_n_pos, h_mem⟩
  kcall beeu_loop_end_correct s trivial with mid_data ⟨h_mid_fr, h_mid_dmem, h_branch⟩
  kframe_eqs h_mid_fr
  by_cases hA : s.regs.beeuA = 1
  · simp only [hA, ↓reduceIte] at h_branch ⊢
    rcases h_branch with ⟨rfl, h_mid_x14⟩
    kcall beeu_reduction_to_return_correct mid_data r₀ o0 o1 o2 o3 R
        ⟨h_sp_align, h_mid_fr_SP.trans h_sp, h_mid_fr_X29.trans h_x29, h_mid_x14,
         h_mid_fr_beeuN.symm ▸ h_n_pos, h_mid_dmem ▸ h_mem⟩
      with fin ⟨h_x0, h_sp', h_x30', h_cs', w0, w1, w2, w3, h_val, h_mem'⟩
    apply Eventually.done
    rw [h_mid_fr_beeuN, h_mid_fr_beeuY] at h_val
    exact ⟨rfl, h_sp', h_x30', h_cs', h_x0, w0, w1, w2, w3, h_val, h_mem'⟩
  · simp only [hA, ↓reduceIte] at h_branch ⊢
    subst h_branch
    have h_mem_mid : (mid_data.dmem =⋆
        BeeuStackFrame r₀ (r₀.SP.toBitVec + 18446744073709551504#64) ⋆
        (Words256At o0 o1 o2 o3 r₀.X0.toBitVec ⋆ R)) := by
      rw [h_mid_dmem]; ecancel
    kcall beeu_epilogue_err_correct mid_data r₀ (Words256At o0 o1 o2 o3 r₀.X0.toBitVec ⋆ R)
        ⟨h_sp_align, h_mid_fr_X29.trans h_x29, h_mem_mid⟩
      with fin ⟨h_x0, h_sp', h_x30', h_cs', h_mem'⟩
    apply Eventually.done
    exact ⟨rfl, h_sp', h_x30', h_cs', h_x0, by ecancel⟩

/-! ## Prologue and Top-Level Specification

`beeu_prologue_correct` is placed immediately before the top-level theorem because its elaboration
(~17s) is the heaviest in the file and Lean kernel-checks declarations in file order. -/

block_spec beeu_prologue_correct beeu_mod_inverse_vartime s₀
  (stack a_bs n_bs : List UInt8) (R : DataMem → Prop)
  to ".Lbeeu_loop"
  (pre :=
    let sp' := s₀.regs.SP.toBitVec + 18446744073709551504#64
    s₀.regs.SP.toBitVec % 16#64 = 0#64 ∧
    stack.length = 112 ∧
    a_bs.length = 32 ∧
    n_bs.length = 32 ∧
    (s₀.dmem =⋆ stack @ sp' ⋆ a_bs @ s₀.regs.X1 ⋆ n_bs @ s₀.regs.X2 ⋆ R))
  (post := fun st =>
    let sp' := s₀.regs.SP.toBitVec + 18446744073709551504#64
    st.data.regs.SP.toBitVec = sp' ∧
    st.data.regs.X29.toBitVec = sp' ∧
    st.data.regs.beeuB = Int.ofBytes a_bs ∧
    st.data.regs.beeuA = Int.ofBytes n_bs ∧
    st.data.regs.beeuN = Int.ofBytes n_bs ∧
    st.data.regs.beeuX = 1 ∧
    st.data.regs.beeuY = 0 ∧
    (st.data.dmem =⋆
      BeeuStackFrame s₀.regs sp' ⋆
      a_bs @ s₀.regs.X1 ⋆ n_bs @ s₀.regs.X2 ⋆ R)) := by
  rintro ⟨h_sp_align, h_stack_len, h_a_len, h_n_len, h_mem⟩
  dsimp only [BeeuStackFrame, BeeuSavedRegs]
  kprologue beeu_mod_inverse_vartime to ".Lbeeu_loop" with s₀
  kfinish beeu_mod_inverse_vartime [Reg64s.beeuB, Reg64s.beeuA, Reg64s.beeuN, Reg64s.beeuX,
    Reg64s.beeuY, sp_sub_112_add_zero]
  · exact val256_of_limbs a_bs h_a_len
  · exact val256_of_limbs n_bs h_n_len
  · exact val256_of_limbs n_bs h_n_len

/-- Top-level end-to-end functional correctness of BoringSSL's `beeu_mod_inverse_vartime`:
    Given a 16-byte-aligned stack with 112 bytes of frame space, 32-byte input buffers `a_bs` at `x1`
    and odd modulus `n_bs` at `x2` with `0 ≤ a ≤ n`, and a 32-byte output buffer at `x0`,
    `beeu_mod_inverse_vartime` terminates and returns to `x30` with `sp` and all callee-saved
    registers (`x19..x29`) restored, and:
    - if `gcd a n = 1`, returns `x0 = 1` and writes 256-bit `out` (`0 < out ≤ n`) to the output buffer
      such that `(a * out) % n = 1 % n` (the modular inverse of `a` modulo `n`),
    - otherwise returns `x0 = 0` with the output buffer unchanged. -/
block_spec beeu_mod_inverse_vartime_correct beeu_mod_inverse_vartime s₀
  (stack a_bs n_bs : List UInt8) (o0 o1 o2 o3 : UInt64) (R : DataMem → Prop)
  (exit := Int64.ofInt s₀.regs.X30.toBitVec.toInt)
  (pre :=
    let sp' := s₀.regs.SP.toBitVec + 18446744073709551504#64
    let a := Int.ofBytes a_bs
    let n := Int.ofBytes n_bs
    s₀.regs.SP.toBitVec % 16#64 = 0#64 ∧
    stack.length = 112 ∧
    a_bs.length = 32 ∧
    n_bs.length = 32 ∧
    a ≤ n ∧
    0 < n ∧
    n % 2 = 1 ∧
    (s₀.dmem =⋆
      stack @ sp' ⋆
      Words256At o0 o1 o2 o3 s₀.regs.X0.toBitVec ⋆
      a_bs @ s₀.regs.X1 ⋆
      n_bs @ s₀.regs.X2 ⋆
      R))
  (post := fun st =>
    let sp' := s₀.regs.SP.toBitVec + 18446744073709551504#64
    let a := Int.ofBytes a_bs
    let n := Int.ofBytes n_bs
    st.data.regs.SP = s₀.regs.SP ∧
    st.data.regs.X30 = s₀.regs.X30 ∧
    st.data.regs.CalleeSavedEq s₀.regs ∧
    if Int.gcd a n = 1 then
      st.data.regs.X0 = 1 ∧
      ∃ w0 w1 w2 w3 : UInt64,
        0 < val256 w0 w1 w2 w3 ∧
        val256 w0 w1 w2 w3 ≤ n ∧
        (a * val256 w0 w1 w2 w3) % n = 1 % n ∧
        (st.data.dmem =⋆
          BeeuStackFrame s₀.regs sp' ⋆
          Words256At w0 w1 w2 w3 s₀.regs.X0.toBitVec ⋆
          a_bs @ s₀.regs.X1 ⋆
          n_bs @ s₀.regs.X2 ⋆
          R)
    else
      st.data.regs.X0 = 0 ∧
      (st.data.dmem =⋆
        BeeuStackFrame s₀.regs sp' ⋆
        Words256At o0 o1 o2 o3 s₀.regs.X0.toBitVec ⋆
        a_bs @ s₀.regs.X1 ⋆
        n_bs @ s₀.regs.X2 ⋆
        R)) := by
  rintro ⟨h_sp_align, h_stack_len, h_a_len, h_n_len, h_a_le, h_n_pos, h_n_odd, h_mem⟩
  let sp' := s₀.regs.SP.toBitVec + 18446744073709551504#64
  let a := Int.ofBytes a_bs
  let n := Int.ofBytes n_bs
  have h_a_nonneg : 0 ≤ a := Int.ofBytes_ge_zero a_bs
  have h_mem_pro : (s₀.dmem =⋆
      stack @ sp' ⋆ a_bs @ s₀.regs.X1 ⋆ n_bs @ s₀.regs.X2 ⋆
      (Words256At o0 o1 o2 o3 s₀.regs.X0.toBitVec ⋆ R)) := by
    ecancel
  kcall beeu_prologue_correct s₀ stack a_bs n_bs (Words256At o0 o1 o2 o3 s₀.regs.X0.toBitVec ⋆ R)
    with st1 ⟨h1_sp, h1_x29, h1_B, h1_A, h1_N, h1_X, h1_Y, h1_mem⟩
  have h1_B_nonneg : 0 ≤ st1.regs.beeuB := val256_nonneg _ _ _ _
  have h1_X_inv : (a * st1.regs.beeuX - st1.regs.beeuB) % st1.regs.beeuN = 0 := by
    rw [h1_X, h1_B]; change (a * 1 - a) % st1.regs.beeuN = 0; simp
  have h1_Y_inv : (a * st1.regs.beeuY + st1.regs.beeuA) % st1.regs.beeuN = 0 := by
    rw [h1_Y, h1_A, h1_N]; change (a * 0 + n) % n = 0; simp
  have h1_I : BeeuInv a st1.regs.beeuN 0 0 st1.regs.beeuB st1.regs.beeuA
      st1.regs.beeuX st1.regs.beeuY := by
    rw [h1_B, h1_A, h1_N, h1_X, h1_Y]
    refine ⟨h_n_odd, Int.gcd_comm _ _, h_a_nonneg, h_a_le, h_n_pos, Int.le_refl _, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
    · change (a * 1 - a) % n = 0; simp
    · change (a * 0 + n) % n = 0; simp
    · simp only [Nat.pow_zero, Int.natCast_one, Int.one_mul]; exact h_a_le
    · simp only [Nat.pow_zero, Int.natCast_one, Int.one_mul]; exact Int.le_refl _
    · rw [beeuBound_zero]; omega
    · intro _; rw [beeuBound_zero]; omega
    · rw [beeuBound_zero]; omega
    · intro _; rw [beeuBound_zero]; omega
  kcall beeu_loop_correct st1 a h1_I with st2 ⟨h2_fr, h2_dmem, h2_A_pos, h2_A_le, h2_Y_inv, h2_gcd⟩
  kframe_eqs h2_fr
  rw [h1_N] at h2_gcd
  have h2_sp_eq : st2.regs.SP = UInt64.ofBitVec sp' :=
    UInt64.eq_of_toBitVec_eq (by rw [h2_fr_SP]; exact h1_sp)
  have h2_x29_eq : st2.regs.X29 = UInt64.ofBitVec sp' :=
    UInt64.eq_of_toBitVec_eq (by rw [h2_fr_X29]; exact h1_x29)
  have h2_mem : (st2.dmem =⋆
      BeeuStackFrame s₀.regs sp' ⋆
      Words256At o0 o1 o2 o3 s₀.regs.X0.toBitVec ⋆
      (a_bs @ s₀.regs.X1 ⋆ n_bs @ s₀.regs.X2 ⋆ R)) := by
    rw [h2_dmem]; ecancel
  kcall beeu_loop_end_to_return_correct st2 s₀.regs o0 o1 o2 o3
      (a_bs @ s₀.regs.X1 ⋆ n_bs @ s₀.regs.X2 ⋆ R)
      ⟨h_sp_align, h2_sp_eq, h2_x29_eq, by rw [h2_fr_beeuN, h1_N]; exact h_n_pos, h2_mem⟩
    with fin ⟨h_fin_sp, h_fin_x30, h_fin_cs, h_fin_branch⟩
  apply Eventually.done
  dsimp only
  refine ⟨rfl, h_fin_sp, h_fin_x30, h_fin_cs, ?_⟩
  split
  · rename_i hg
    have hA1 : st2.regs.beeuA = 1 := h2_gcd.mpr hg
    simp only [hA1, ↓reduceIte] at h_fin_branch
    rcases h_fin_branch with ⟨h_x0, w0, w1, w2, w3, h_val, h_mem'⟩
    have h_inv1 : (a * st2.regs.beeuY + 1) % n = 0 := by
      rw [hA1, h1_N] at h2_Y_inv; exact h2_Y_inv
    have h_val_n : val256 w0 w1 w2 w3 = n - (st2.regs.beeuY % n) := by
      rw [h2_fr_beeuN, h1_N] at h_val; exact h_val
    have ⟨h_out_pos, h_out_le, h_out_inv⟩ :=
      mod_inv_of_beeu_end a st2.regs.beeuY (val256 w0 w1 w2 w3) n h_n_pos h_inv1 h_val_n
    exact ⟨h_x0, w0, w1, w2, w3, h_out_pos, h_out_le, h_out_inv, by ecancel⟩
  · rename_i hg
    have hA1 : ¬ st2.regs.beeuA = 1 := fun h => hg (h2_gcd.mp h)
    simp only [hA1, ↓reduceIte] at h_fin_branch
    rcases h_fin_branch with ⟨h_x0, h_mem'⟩
    exact ⟨h_x0, by ecancel⟩
