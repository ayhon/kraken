module

import Kraken.BitVecArith

/-!
# Tests for `Kraken.BitVecArith`

Usage examples for the instruction-level `toNat` lemmas at several widths, and checks that the
typical downstream goals close with `omega`/`grind` (no `bv_decide`).
-/

open BitVec

/-! ### Funnel shifts (`extr`, `lsr`/`lsl` by register) -/

-- `extr x, hi, lo, #1` as a number, 64-bit.
example (hi lo : BitVec 64) :
    ((lo >>> 1) ||| (hi <<< 63)).toNat = lo.toNat / 2 + 2 ^ 63 * (hi.toNat % 2) := by
  rw [toNat_funnel_nat' lo hi (k := 1) (m := 63) rfl]
  omega

-- Same at 32 bits (`W` registers).
example (hi lo : BitVec 32) :
    ((lo >>> 5) ||| (hi <<< 27)).toNat = lo.toNat / 32 + (hi.toNat % 32) * 2 ^ 27 :=
  toNat_funnel_nat' lo hi (k := 5) (m := 27) rfl

-- `k = 0` is allowed: the shifted-in half vanishes.
example (hi lo : BitVec 16) : ((lo >>> 0) ||| (hi <<< 16)).toNat = lo.toNat := by
  rw [toNat_funnel_nat lo hi (k := 0) (by omega)]
  simp only [Nat.pow_zero, Nat.div_one, Nat.mod_one, Nat.zero_mul, Nat.add_zero]

-- Variable shift amounts from registers: `(lo >> k) | (hi << (-k))`.
example (lo hi k : BitVec 64) (hk1 : 1#64 ≤ k) (hk63 : k ≤ 63#64) :
    ((lo >>> (k % 64#64)) ||| (hi <<< ((0#64 - k) % 64#64))).toNat < 2 ^ 64 := by
  rw [toNat_funnel lo hi hk1 hk63]
  have hk := toNat_le_63 hk63
  have hpq := two_pow_mul_two_pow_sub hk63
  have hA : lo.toNat / 2 ^ k.toNat < 2 ^ (64 - k.toNat) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.mul_comm, hpq]; exact lo.isLt
  have hB : hi.toNat % 2 ^ k.toNat < 2 ^ k.toNat := Nat.mod_lt _ (Nat.two_pow_pos _)
  have : (hi.toNat % 2 ^ k.toNat + 1) * 2 ^ (64 - k.toNat) ≤ 2 ^ k.toNat * 2 ^ (64 - k.toNat) :=
    Nat.mul_le_mul_right _ hB
  rw [hpq, Nat.add_mul, Nat.one_mul] at this
  omega

-- `grind` finds `toNat_funnel_nat'` by E-matching and discharges `1 + 63 = 64` itself.
example (hi lo : UInt64) :
    (UInt64.ofBitVec (lo.toBitVec >>> 1 ||| hi.toBitVec <<< 63)).toNat =
      lo.toNat / 2 + 2 ^ 63 * (hi.toNat % 2) := by
  grind

/-! ### Immediate shifts (`ubfm`/`lsr #k`) -/

example (x : BitVec 64) : setWidth 64 (extractLsb' 0 63 (x >>> 1)) = x >>> 1 := by
  grind

example (x : BitVec 64) : setWidth 64 (extractLsb' 0 63 (x >>> 1)) = x >>> 1 :=
  setWidth_extractLsb'_ushiftRight x (by decide)

example (x : BitVec 32) : setWidth 32 (extractLsb' 0 20 (x >>> 12)) = x >>> 12 :=
  setWidth_extractLsb'_ushiftRight x (by decide)

/-! ### Masks -/

example (x k : BitVec 64) (hk63 : k ≤ 63#64) :
    (x &&& ((1#64 <<< k) - 1#64)).toNat < 2 ^ k.toNat := by
  rw [toNat_and_mask x hk63]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

-- Page + 12-bit offset reconstruction (`adrp` + `:lo12:`).
example (x : BitVec 64) : (x &&& ~~~0xFFF#64) + (x &&& 0xFFF#64) = x := by
  simp

example (x : BitVec 64) :
    (x &&& 18446744073709547520#64) +
      BitVec.ofInt 64 (Int64.ofNat (x &&& 4095#64).toNat).toInt = x := by
  simp

/-! ### Clamped count-trailing-zeros (`rbit; orr #1; clz`) -/

example (x : BitVec 64) : (x.reverse ||| 1#64).clz ≤ 63#64 := clz_reverse_or_one_le_63 x

example (x : BitVec 32) : (x.reverse ||| 1#32).clz < 32#32 := clz_reverse_or_one_lt x (by decide)

-- The low `c` bits of `x` are clear: `x = 2^c * (x / 2^c)`.
example (x : BitVec 64) :
    x.toNat = 2 ^ ((x.reverse ||| 1#64).clz).toNat * (x.toNat / 2 ^ ((x.reverse ||| 1#64).clz).toNat) := by
  have h := toNat_mod_two_pow_clz_reverse_or_one x (by decide)
  have := Nat.div_add_mod x.toNat (2 ^ ((x.reverse ||| 1#64).clz).toNat)
  omega

-- Unless clamped, bit `c` is set, i.e. `x / 2^c` is odd.
example (x : BitVec 64) :
    (x.toNat / 2 ^ ((x.reverse ||| 1#64).clz).toNat) % 2 = 1 ∨ (x.reverse ||| 1#64).clz = 63#64 := by
  rcases getLsbD_clz_reverse_or_one_64 x with h | h
  · left
    rw [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq] at h
    exact h
  · right
    exact h

-- A zero count means the word is odd (bit 0 set); clamping cannot interfere for `1 < w`.
example (x : BitVec 64) (h : (x.reverse ||| 1#64).clz = 0#64) : x.toNat % 2 = 1 := by
  have := getLsbD_zero_of_clz_reverse_or_one_eq_zero (by decide) h
  rw [BitVec.getLsbD, Nat.testBit_zero, decide_eq_true_eq] at this
  exact this
