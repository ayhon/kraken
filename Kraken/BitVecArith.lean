module

import Kraken.Attribute

/-!
# Bit-Vector and Multi-Limb Arithmetic

Instruction-level identities relating `BitVec` sub-word operations, shifts, masks, funnel shifts,
and the `rbit`/`clz` trailing-zero idiom to `Nat` and `Int` arithmetic (`/ 2^k`, `% 2^k`,
`* 2^(64-k)`), together with value-level characterizations of processor status flags and condition
codes. They let multi-limb proofs stay at the `Nat`/`Int` level (`omega`, `grind`) instead of
running `bv_decide` on wide multiplications.

Policy for `bv_decide` in Kraken proofs: avoid it. Every call adds a trusted
`*._native.bv_decide.ax` axiom (the SAT certificate checker runs as native code) and its cost
grows quickly with width and with `*`/`/`. Prefer `grind` (linear `BitVec` arithmetic, `|||`/`=0`
reasoning), `omega` on `toNat` images, and the lemmas below; if `bv_decide` is still needed, keep
it to facts at most 64 bits wide with no non-constant multiplication or division (milliseconds).
-/

@[expose] public section

-- Injective coercions only.
attribute [-instance] BitVec.instNatCast
attribute [-instance] BitVec.instIntCast
instance : Coe Bool Nat where coe := Bool.toNat

attribute [kstep]
  BitVec.extractLsb'
  BitVec.truncate
  Int64.toInt
  Int.toNat

attribute [simp, ksimp, grind =]
  BitVec.ofNat_and

attribute [ksimp, grind =]
  BitVec.ofInt_add
  BitVec.ofInt_toInt
  BitVec.ofNat_toNat
  BitVec.setWidth_eq
  BitVec.shiftLeft_zero
  BitVec.zero_or
  BitVec.or_zero
  Int64.ofInt_bitVecToInt
  Int64.ofInt_toInt
  Int64.toBitVec_ofNat'
  Int64.toInt_ofNat'
  Int64.toInt_zero
  Int64.toInt_one

@[simp, ksimp]
theorem Int64.add_sub_cancel' (a b : Int64) : a + (b - a) = b := by
  grind

@[simp, ksimp, grind =]
theorem Int64.ofInt_toInt_eq_toBitVec (i : Int64) : BitVec.ofInt 64 i.toInt = i.toBitVec :=
  BitVec.ofInt_toInt

@[simp, ksimp, grind =]
theorem Int64.ofInt_bmod_size_natCast (n : Nat) :
    BitVec.ofInt 64 ((n : Int).bmod Int64.size) = BitVec.ofNat 64 n := by
  rw [← Int64.toInt_ofNat']
  exact BitVec.ofInt_toInt

@[simp, ksimp, grind =]
theorem Int64.toBitVec_ofNat_toNat (x : BitVec 64) : (Int64.ofNat x.toNat).toBitVec = x := by
  simp

@[simp, ksimp, grind =]
theorem Int64.ofInt_toInt_ofNat_toNat (x : BitVec 64) :
    BitVec.ofInt 64 (Int64.ofNat x.toNat).toInt = x := by
  simp

namespace BitVec

variable {w : Nat}

/-! ### Sub-word extraction, extension, and lane operations -/

@[kstep] def unsigned (x : BitVec w) : Int := x.toNat
@[kstep] def signed (x : BitVec w) : Int := x.toInt
@[kstep] def take (x : BitVec w) (n : Nat) : BitVec n := x.extractLsb' 0 n
@[kstep] def drop (x : BitVec w) (n : Nat) : BitVec (w - n) := x.extractLsb' n (w - n)

/-- Replace the low `n` bits of `old` with `new`. -/
def replaceLow {n : Nat} (old : BitVec w) (new : BitVec n) : BitVec w :=
  (BitVec.append (old.drop n) new).setWidth w

/-- Population count recurrence over the low `pos` bits of `x`. -/
def cpopNatRec_ (x : BitVec w) (pos acc : Nat) : Nat :=
  match pos with
  | 0 => acc
  | n + 1 => x.cpopNatRec_ n (acc + (x.getLsbD n).toNat)

/-- Population count of `x` as a `w`-bit vector. -/
def cpop_ (x : BitVec w) : BitVec w := BitVec.ofNat w (cpopNatRec_ x w 0)

/-- Apply a binary operation `op` lane-wise to `c`-bit chunks of `a` and `b`. -/
def packedBinOp {w : Nat} (c : Nat) (op : BitVec c → BitVec c → BitVec c) (a b : BitVec w) : BitVec w :=
  if _h : c = 0 ∨ w < c then
    a
  else
    let res_low := op (a.take c) (b.take c)
    let res_high := BitVec.packedBinOp c op (a.drop c) (b.drop c)
    (BitVec.append res_high res_low).setWidth w
termination_by w
decreasing_by omega

def toFloat32 (v : BitVec 32) : Float32 :=
  Float32.ofBits (UInt32.ofBitVec v)

def _root_.Float32.toBitVec (f : Float32) : BitVec 32 :=
  UInt32.toBitVec (Float32.toBits f)

@[simp, ksimp, grind =]
theorem extractLsb'_self (x : BitVec w) : x.extractLsb' 0 w = x := by
  simp

theorem zeroExtend_zeroExtend_of_le {m n : Nat} (v : BitVec w) (h : w ≤ m := by decide) :
    (v.zeroExtend m).zeroExtend n = v.zeroExtend n := by
  ext i hi; simp [BitVec.zeroExtend]; grind

@[simp, ksimp]
theorem zeroExtend_64_zeroExtend_32_8 (v : BitVec 8) :
    (v.zeroExtend 32).zeroExtend 64 = v.zeroExtend 64 :=
  zeroExtend_zeroExtend_of_le v

@[simp, ksimp]
theorem zeroExtend_64_zeroExtend_32_16 (v : BitVec 16) :
    (v.zeroExtend 32).zeroExtend 64 = v.zeroExtend 64 :=
  zeroExtend_zeroExtend_of_le v

@[simp, ksimp]
theorem extractLsb'_8_extractLsb'_32 (v : BitVec w) :
    (v.extractLsb' 0 32).extractLsb' 0 8 = v.extractLsb' 0 8 :=
  BitVec.extractLsb'_extractLsb'_of_le (by decide)

@[simp, ksimp]
theorem extractLsb'_16_extractLsb'_32 (v : BitVec w) :
    (v.extractLsb' 0 32).extractLsb' 0 16 = v.extractLsb' 0 16 :=
  BitVec.extractLsb'_extractLsb'_of_le (by decide)

@[simp, ksimp]
theorem setWidth_8_setWidth_32 (v : BitVec w) :
    BitVec.setWidth 8 (BitVec.setWidth 32 v) = BitVec.setWidth 8 v :=
  BitVec.setWidth_setWidth_of_le v (by decide)

@[simp, ksimp]
theorem setWidth_16_setWidth_32 (v : BitVec w) :
    BitVec.setWidth 16 (BitVec.setWidth 32 v) = BitVec.setWidth 16 v :=
  BitVec.setWidth_setWidth_of_le v (by decide)

theorem extractLsb'_zeroExtend_of_le {m : Nat} (v : BitVec w) (h : w ≤ m := by decide) :
    (v.zeroExtend m).extractLsb' 0 w = v := by
  ext i hi; simp [BitVec.zeroExtend]; grind

@[simp, ksimp]
theorem extractLsb'_8_zeroExtend_64 (v : BitVec 8) :
    (v.zeroExtend 64).extractLsb' 0 8 = v :=
  extractLsb'_zeroExtend_of_le v

@[simp, ksimp]
theorem extractLsb'_16_zeroExtend_64 (v : BitVec 16) :
    (v.zeroExtend 64).extractLsb' 0 16 = v :=
  extractLsb'_zeroExtend_of_le v

@[simp, ksimp]
theorem extractLsb'_32_zeroExtend_64 (v : BitVec 32) :
    (v.zeroExtend 64).extractLsb' 0 32 = v :=
  extractLsb'_zeroExtend_of_le v

@[simp, ksimp]
theorem setWidth_8_setWidth_64 (v : BitVec 8) :
    BitVec.setWidth 8 (BitVec.setWidth 64 v) = v :=
  extractLsb'_zeroExtend_of_le v

@[simp, ksimp]
theorem setWidth_16_setWidth_64 (v : BitVec 16) :
    BitVec.setWidth 16 (BitVec.setWidth 64 v) = v :=
  extractLsb'_zeroExtend_of_le v

@[simp, ksimp]
theorem setWidth_32_setWidth_64 (v : BitVec 32) :
    BitVec.setWidth 32 (BitVec.setWidth 64 v) = v :=
  extractLsb'_zeroExtend_of_le v

theorem setWidth_replaceLow {n : Nat} (old : BitVec w) (v : BitVec n) (h : n ≤ w := by decide) :
    BitVec.setWidth n (old.replaceLow v) = v := by
  ext i hi
  simp [BitVec.replaceLow, BitVec.drop, BitVec.getLsbD_append]
  grind

@[simp, ksimp]
theorem setWidth_8_replaceLow_8 (old : BitVec 64) (v : BitVec 8) :
    BitVec.setWidth 8 (old.replaceLow v) = v :=
  setWidth_replaceLow old v

@[simp, ksimp]
theorem setWidth_16_replaceLow_16 (old : BitVec 64) (v : BitVec 16) :
    BitVec.setWidth 16 (old.replaceLow v) = v :=
  setWidth_replaceLow old v

@[ksimp, grind =]
theorem ofNat_sub_of_le (x y : Nat) (h : y ≤ x) :
    BitVec.ofNat w (x - y) = BitVec.ofNat w x - BitVec.ofNat w y := by
  have := congrArg (BitVec.ofNat w) (Nat.sub_add_cancel h)
  rw [BitVec.ofNat_add] at this
  grind

theorem add_add_eq_of_add_eq (base a b c : BitVec w) (h : a + b = c) :
    (base + a) + b = base + c := by
  rw [BitVec.add_assoc, h]

theorem add_eq_add_add_of_add_eq (base a b c : BitVec w) (h : a + b = c) :
    base + c = (base + a) + b := by
  rw [BitVec.add_assoc, h]

/-- Full-width register read in `BitVec` form: `BitVec.ofNat 64 x.toNat` is `x.toBitVec`. -/
theorem _root_.UInt64.bitVecOfNat_toNat (x : UInt64) : BitVec.ofNat 64 x.toNat = x.toBitVec :=
  BitVec.eq_of_toNat_eq (by simp)

theorem _root_.UInt32.bitVecOfNat_toNat (x : UInt32) : BitVec.ofNat 32 x.toNat = x.toBitVec :=
  BitVec.eq_of_toNat_eq (by simp)

/-! ### Shift and mask arithmetic -/

/-- Complementary bitmasks sum to the original value: `(x &&& ~~~m) + (x &&& m) = x`. -/
@[simp, ksimp, grind =]
theorem add_and_not_and (x m : BitVec w) : (x &&& ~~~m) + (x &&& m) = x := by
  have hdisj : (x &&& ~~~m) &&& (x &&& m) = 0#w := by
    ext i hi
    simp
    grind
  rw [BitVec.add_eq_or_of_and_eq_zero _ _ hdisj]
  ext i hi
  simp
  grind

@[simp, ksimp, grind =]
theorem add_and_not_and' (x m : BitVec w) : (x &&& m) + (x &&& ~~~m) = x := by
  rw [BitVec.add_comm, add_and_not_and]

@[simp, ksimp, grind =]
theorem add_and_not_and_assoc (x m y : BitVec w) :
    (x &&& ~~~m) + ((x &&& m) + y) = x + y := by
  rw [← BitVec.add_assoc, add_and_not_and]

/-- Ground-evaluated 4 KB page + 12-bit offset reconstruction (`~~~0xFFF#64 = 0xFFFFFFFFFFFFF000#64`),
matching `Sym.dsimp` evaluation of `adrp` + `:lo12:`. -/
@[simp, ksimp, grind =]
theorem add_and_page_lo12 (x : BitVec 64) :
    (x &&& 0xFFFFFFFFFFFFF000#64) + (x &&& 0xFFF#64) = x :=
  add_and_not_and x 0xFFF#64

@[simp, ksimp, grind =]
theorem add_and_lo12_page (x : BitVec 64) :
    (x &&& 0xFFF#64) + (x &&& 0xFFFFFFFFFFFFF000#64) = x :=
  add_and_not_and' x 0xFFF#64

@[simp, ksimp, grind =]
theorem add_and_page_lo12_assoc (x y : BitVec 64) :
    (x &&& 0xFFFFFFFFFFFFF000#64) + ((x &&& 0xFFF#64) + y) = x + y :=
  add_and_not_and_assoc x 0xFFF#64 y

@[simp, ksimp, grind =]
theorem and_page_idem (x : BitVec 64) :
    x &&& 0xFFFFFFFFFFFFF000#64 &&& 0xFFFFFFFFFFFFF000#64 = x &&& 0xFFFFFFFFFFFFF000#64 := by
  rw [BitVec.and_assoc, BitVec.and_self]

@[simp, ksimp, grind =]
theorem and_lo12_idem (x : BitVec 64) :
    x &&& 0xFFF#64 &&& 0xFFF#64 = x &&& 0xFFF#64 := by
  rw [BitVec.and_assoc, BitVec.and_self]

theorem umod_64_eq_self {k : BitVec 64} (hk63 : k ≤ 63#64) : k % 64#64 = k := by grind

theorem toNat_le_63 {k : BitVec 64} (hk63 : k ≤ 63#64) : k.toNat ≤ 63 := by
  simpa [BitVec.le_def] using hk63

theorem one_le_toNat {k : BitVec 64} (hk1 : 1#64 ≤ k) : 1 ≤ k.toNat := by
  simpa [BitVec.le_def] using hk1

theorem neg_umod_64 {k : BitVec 64} (hk1 : 1#64 ≤ k) (hk63 : k ≤ 63#64) :
    (0#64 - k) % 64#64 = 64#64 - k := by grind

theorem toNat_neg_umod_64 {k : BitVec 64} (hk1 : 1#64 ≤ k) (hk63 : k ≤ 63#64) :
    ((0#64 - k) % 64#64).toNat = 64 - k.toNat := by
  have hk := toNat_le_63 hk63
  rw [neg_umod_64 hk1 hk63, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat]
  omega

theorem two_pow_le_two_pow_63 {k : BitVec 64} (hk63 : k ≤ 63#64) : 2 ^ k.toNat ≤ 2 ^ 63 :=
  Nat.pow_le_pow_right (by decide) (toNat_le_63 hk63)

/-- `1 << k` as a natural number. -/
theorem toNat_one_shiftLeft {k : BitVec 64} (hk63 : k ≤ 63#64) :
    (1#64 <<< k).toNat = 2 ^ k.toNat := by
  have hk := toNat_le_63 hk63
  rw [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  have : 1 % 2 ^ 64 = 1 := by decide
  rw [this, Nat.one_mul]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))

/-- The mask `(1 << k) - 1` as a natural number. -/
theorem toNat_mask {k : BitVec 64} (hk63 : k ≤ 63#64) :
    ((1#64 <<< k) - 1#64).toNat = 2 ^ k.toNat - 1 := by
  rw [BitVec.toNat_sub, toNat_one_shiftLeft hk63, BitVec.toNat_ofNat]
  have : 1 % 2 ^ 64 = 1 := by decide
  rw [this]
  have hp_pos : 0 < 2 ^ k.toNat := Nat.two_pow_pos _
  have hp_le := two_pow_le_two_pow_63 hk63
  omega

/-- `x & ((1 << k) - 1) = x mod 2^k`. -/
theorem toNat_and_mask (x : BitVec 64) {k : BitVec 64} (hk63 : k ≤ 63#64) :
    (x &&& ((1#64 <<< k) - 1#64)).toNat = x.toNat % 2 ^ k.toNat := by
  rw [BitVec.toNat_and, toNat_mask hk63, Nat.and_two_pow_sub_one_eq_mod]

/-- `x >> k = x / 2^k`. -/
theorem toNat_ushiftRight_bv (x k : BitVec 64) :
    (x >>> k).toNat = x.toNat / 2 ^ k.toNat := by
  rw [BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- Extracting the low `m ≥ w - k` bits of `x >>> k` and re-extending to `w` bits is the identity
(the top `k` bits are already zero). -/
@[grind =]
theorem setWidth_extractLsb'_ushiftRight (x : BitVec w) {k m : Nat} (h : w ≤ m + k) :
    BitVec.setWidth w (BitVec.extractLsb' 0 m (x >>> k)) = x >>> k := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight,
    Nat.shiftRight_zero, Nat.shiftRight_eq_div_pow]
  have hlt : x.toNat / 2 ^ k < 2 ^ m := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
    exact Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) h)
  rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt]
  exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt

@[simp, ksimp, grind =]
theorem zeroExtend_64_extractLsb'_63_ushiftRight_1 (v : BitVec 64) :
    ((v >>> 1).extractLsb' 0 63).zeroExtend 64 = v >>> 1 :=
  setWidth_extractLsb'_ushiftRight v (by decide)

@[simp, ksimp, grind =]
theorem setWidth_64_setWidth_63_ushiftRight_1 (v : BitVec 64) :
    BitVec.setWidth 64 (BitVec.setWidth 63 (v >>> 1)) = v >>> 1 := by
  ext i hi; simp; grind

theorem two_pow_mul_two_pow_sub {k : BitVec 64} (hk63 : k ≤ 63#64) :
    2 ^ k.toNat * 2 ^ (64 - k.toNat) = 2 ^ 64 := by
  have hk := toNat_le_63 hk63
  rw [← Nat.pow_add]; congr 1; omega

/-- `x << (64 - k) = (x mod 2^k) · 2^(64-k)`. -/
theorem toNat_shiftLeft_neg (x : BitVec 64) {k : BitVec 64} (hk1 : 1#64 ≤ k) (hk63 : k ≤ 63#64) :
    (x <<< ((0#64 - k) % 64#64)).toNat = (x.toNat % 2 ^ k.toNat) * 2 ^ (64 - k.toNat) := by
  rw [BitVec.shiftLeft_eq', toNat_neg_umod_64 hk1 hk63, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    ← two_pow_mul_two_pow_sub hk63, Nat.mul_mod_mul_right]

/-! ### Funnel shifts

`(lo >> k) | (hi << (w - k))` concatenates the top `w - k` bits of `lo` with the low `k` bits of
`hi`. The two halves occupy disjoint bit ranges, so `|||` is `+` and the result is
`lo / 2^k + (hi mod 2^k) · 2^(w-k)` with no overflow. -/

/-- Funnel shift with `Nat` shift amounts `k` and `m`, `k + m = w`. -/
@[grind =]
theorem toNat_funnel_nat' (lo hi : BitVec w) {k m : Nat} (hkm : k + m = w) :
    ((lo >>> k) ||| (hi <<< m)).toNat = lo.toNat / 2 ^ k + (hi.toNat % 2 ^ k) * 2 ^ m := by
  rw [BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq]
  have hpq : 2 ^ k * 2 ^ m = 2 ^ w := by rw [← Nat.pow_add, hkm]
  rw [← hpq, Nat.mul_mod_mul_right]
  have hA : lo.toNat / 2 ^ k < 2 ^ m := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.mul_comm, hpq]; exact lo.isLt
  have h := Nat.two_pow_add_eq_or_of_lt hA (hi.toNat % 2 ^ k)
  rw [Nat.mul_comm (hi.toNat % 2 ^ k), Nat.or_comm, ← h]
  omega

/-- Funnel shift with `Nat` shift amounts `k` and `w - k`. -/
theorem toNat_funnel_nat (lo hi : BitVec w) {k : Nat} (hkw : k ≤ w) :
    ((lo >>> k) ||| (hi <<< (w - k))).toNat =
      lo.toNat / 2 ^ k + (hi.toNat % 2 ^ k) * 2 ^ (w - k) :=
  toNat_funnel_nat' lo hi (by omega)

/-- Funnel shift with 64-bit register shift amounts `k % 64` and `(-k) % 64`. -/
theorem toNat_funnel (lo hi : BitVec 64) {k : BitVec 64} (hk1 : 1#64 ≤ k) (hk63 : k ≤ 63#64) :
    ((lo >>> (k % 64#64)) ||| (hi <<< ((0#64 - k) % 64#64))).toNat =
      lo.toNat / 2 ^ k.toNat + (hi.toNat % 2 ^ k.toNat) * 2 ^ (64 - k.toNat) := by
  rw [BitVec.ushiftRight_eq', BitVec.shiftLeft_eq', umod_64_eq_self hk63,
    toNat_neg_umod_64 hk1 hk63]
  have hk := toNat_le_63 hk63
  exact toNat_funnel_nat lo hi (by omega)

/-- Multi-limb funnel-shift limb identity: multiplying `(lo >> k) | (hi << (-k))` by `2^k` and
adding the low `k` bits of `lo` yields `lo + 2^64 · (low k bits of hi)`. -/
theorem toNat_funnel_mul_add_and_mask (lo hi : BitVec 64) {k : BitVec 64}
    (hk1 : 1#64 ≤ k) (hk63 : k ≤ 63#64) :
    let mask := (1#64 <<< (k % 64#64)) - 1#64
    2 ^ k.toNat * ((lo >>> (k % 64#64)) ||| (hi <<< ((0#64 - k) % 64#64))).toNat +
      (lo &&& mask).toNat =
      lo.toNat + 2 ^ 64 * (hi &&& mask).toNat := by
  dsimp only
  rw [toNat_funnel lo hi hk1 hk63, umod_64_eq_self hk63, toNat_and_mask lo hk63,
    toNat_and_mask hi hk63]
  have := two_pow_mul_two_pow_sub hk63
  have := Nat.div_add_mod lo.toNat (2 ^ k.toNat)
  grind

/-- Multi-limb right-shift top-limb identity: multiplying `hi >> k` by `2^k` and adding the low
`k` bits of `hi` reconstructs `hi`. -/
theorem toNat_ushiftRight_mul_add_and_mask (hi : BitVec 64) {k : BitVec 64}
    (hk63 : k ≤ 63#64) :
    let mask := (1#64 <<< (k % 64#64)) - 1#64
    2 ^ k.toNat * (hi >>> (k % 64#64)).toNat + (hi &&& mask).toNat = hi.toNat := by
  dsimp only
  rw [BitVec.ushiftRight_eq', umod_64_eq_self hk63, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, toNat_and_mask hi hk63]
  exact Nat.div_add_mod hi.toNat (2 ^ k.toNat)

/-! ### Clamped count-trailing-zeros: `rbit; orr #1; clz`

`(x.reverse ||| 1).clz` is `min (ctz x) (w - 1)`, the clamped trailing-zero count computed by the
`rbit`/`orr`/`clz` idiom (forcing bit `w - 1` of the reversed word makes `clz` well defined for
`x = 0` and bounds the result by `w - 1`). -/

/-- Bits of `(x.reverse ||| 1).reverse`: `x` with bit `w - 1` forced. -/
theorem getLsbD_reverse_or_one_reverse (x : BitVec w) (i : Nat) (hw : 0 < w) :
    (x.reverse ||| 1#w).reverse.getLsbD i = (x.getLsbD i || decide (i = w - 1)) := by
  rw [BitVec.getLsbD_reverse, BitVec.getMsbD_or, BitVec.getMsbD_reverse, BitVec.getMsbD_eq_getLsbD,
    BitVec.getLsbD_one]
  by_cases hi : i < w
  · have : (w - 1 - i = 0) ↔ (i = w - 1) := by omega
    simp [hi, hw, this]
  · have hx : x.getLsbD i = false := BitVec.getLsbD_of_ge x i (by omega)
    have : ¬ (i = w - 1) := by omega
    simp [hi, hx, this]

theorem reverse_or_one_reverse_ne_zero (x : BitVec w) (hw : 0 < w) :
    (x.reverse ||| 1#w).reverse ≠ 0#w := by
  intro h
  have := getLsbD_reverse_or_one_reverse x (w - 1) hw
  rw [h] at this
  simp at this

/-- The clamped count is `< w`. -/
theorem clz_reverse_or_one_lt (x : BitVec w) (hw : 0 < w) :
    (x.reverse ||| 1#w).clz < BitVec.ofNat w w := by
  rw [BitVec.clz_eq_reverse_ctz]
  exact BitVec.ctz_lt_iff_ne_zero.mpr (reverse_or_one_reverse_ne_zero x hw)

theorem toNat_clz_reverse_or_one_lt (x : BitVec w) (hw : 0 < w) :
    ((x.reverse ||| 1#w).clz).toNat < w := by
  have h := BitVec.lt_def.mp (clz_reverse_or_one_lt x hw)
  rw [BitVec.toNat_ofNat] at h
  exact Nat.lt_of_lt_of_le h (Nat.mod_le _ _)

/-- The clamped count is `≤ 63` for 64-bit words. -/
theorem clz_reverse_or_one_le_63 (x : BitVec 64) : (x.reverse ||| 1#64).clz ≤ 63#64 := by
  have h := toNat_clz_reverse_or_one_lt x (by decide)
  rw [BitVec.le_def]
  change _ ≤ 63
  omega

/-- The bits of `x` below the clamped count are clear. -/
theorem getLsbD_false_of_lt_clz_reverse_or_one {x : BitVec w} {i : Nat} (hw : 0 < w)
    (hi : i < ((x.reverse ||| 1#w).clz).toNat) : x.getLsbD i = false := by
  rw [BitVec.clz_eq_reverse_ctz] at hi
  have h := BitVec.getLsbD_false_of_lt_ctz hi
  rw [getLsbD_reverse_or_one_reverse x i hw] at h
  exact (Bool.or_eq_false_iff.mp h).1

/-- `x mod 2^c = 0` for the clamped count `c`. -/
theorem toNat_mod_two_pow_clz_reverse_or_one (x : BitVec w) (hw : 0 < w) :
    x.toNat % 2 ^ ((x.reverse ||| 1#w).clz).toNat = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
  by_cases hi : i < ((x.reverse ||| 1#w).clz).toNat
  · have h := getLsbD_false_of_lt_clz_reverse_or_one hw hi
    simp only [hi, decide_true, Bool.true_and]
    exact h
  · simp [hi]

/-- Bit `c` of `x` is set unless the count was clamped (`c = w - 1`). -/
theorem getLsbD_clz_reverse_or_one (x : BitVec w) (hw : 0 < w) :
    x.getLsbD ((x.reverse ||| 1#w).clz).toNat = true ∨ ((x.reverse ||| 1#w).clz).toNat = w - 1 := by
  rw [BitVec.clz_eq_reverse_ctz]
  have h := BitVec.getLsbD_true_ctz_of_ne_zero (reverse_or_one_reverse_ne_zero x hw)
  rw [getLsbD_reverse_or_one_reverse x _ hw, Bool.or_eq_true, decide_eq_true_eq] at h
  exact h

/-- 64-bit form of `getLsbD_clz_reverse_or_one`. -/
theorem getLsbD_clz_reverse_or_one_64 (x : BitVec 64) :
    x.getLsbD ((x.reverse ||| 1#64).clz).toNat = true ∨ (x.reverse ||| 1#64).clz = 63#64 := by
  rcases getLsbD_clz_reverse_or_one x (by decide) with h | h
  · exact Or.inl h
  · exact Or.inr (BitVec.eq_of_toNat_eq h)

/-- After funnel-shifting `b0` and `b1` by `k = (b0.reverse ||| 1).clz`, bit 0 is set unless
`k` was clamped to `63`. -/
theorem shift256Word_lsb_or_clamped (b0 b1 : BitVec 64) :
    let k := (b0.reverse ||| 1#64).clz
    ((b0 >>> (k % 64#64)) ||| (b1 <<< ((0#64 - k) % 64#64))).getLsbD 0 = true ∨ k = 63#64 := by
  intro k
  have hk63 : k ≤ 63#64 := clz_reverse_or_one_le_63 b0
  rw [BitVec.getLsbD_or, BitVec.ushiftRight_eq', BitVec.getLsbD_ushiftRight,
    umod_64_eq_self hk63, Nat.add_zero]
  rcases getLsbD_clz_reverse_or_one_64 b0 with h | h
  · exact Or.inl (by rw [h, Bool.true_or])
  · exact Or.inr h

/-- If the clamped count is zero then bit 0 of `x` is set (for `1 < w`). -/
theorem getLsbD_zero_of_clz_reverse_or_one_eq_zero {x : BitVec w} (hw : 1 < w)
    (h : (x.reverse ||| 1#w).clz = 0#w) : x.getLsbD 0 = true := by
  have hc : ((x.reverse ||| 1#w).clz).toNat = 0 := by rw [h]; simp
  rcases getLsbD_clz_reverse_or_one x (by omega) with h' | h'
  · rwa [hc] at h'
  · omega

/-- `x &&& ((1 <<< c) - 1) = 0` for the clamped count `c` (64-bit form). -/
theorem and_mask_clz_reverse_or_one (x : BitVec 64) :
    x &&& ((1#64 <<< ((x.reverse ||| 1#64).clz % 64#64)) - 1#64) = 0#64 := by
  have hk63 := clz_reverse_or_one_le_63 x
  apply BitVec.eq_of_toNat_eq
  rw [umod_64_eq_self hk63, toNat_and_mask x hk63, toNat_mod_two_pow_clz_reverse_or_one x (by decide)]
  rfl

/-! ### Processor flags and carry-chain identities

Helpers for presenting processor flags (carry, borrow, overflow, condition codes) as decided
value-level facts: `BitVec` addition/subtraction as `Nat` case disjunctions, `Int.bmod` facts for
signed overflow, carry/overflow equalities shared across architectures, and the compare idiom. -/

/-- `(x + y).toNat` is the exact sum, or the exact sum minus `2^w` on carry-out. -/
theorem toNat_add_cases (x y : BitVec w) :
    (x.toNat + y.toNat < 2 ^ w ∧ (x + y).toNat = x.toNat + y.toNat) ∨
    (2 ^ w ≤ x.toNat + y.toNat ∧ (x + y).toNat + 2 ^ w = x.toNat + y.toNat) := by
  have hx := x.isLt
  have hy := y.isLt
  by_cases h : x.toNat + y.toNat < 2 ^ w
  · exact Or.inl ⟨h, BitVec.toNat_add_of_lt h⟩
  · refine Or.inr ⟨by omega, ?_⟩
    rw [BitVec.toNat_add, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-- `(x - y).toNat` is the exact difference, or the exact difference plus `2^w` on borrow. -/
theorem toNat_sub_cases (x y : BitVec w) :
    (y.toNat ≤ x.toNat ∧ (x - y).toNat + y.toNat = x.toNat) ∨
    (x.toNat < y.toNat ∧ (x - y).toNat + y.toNat = x.toNat + 2 ^ w) := by
  have hx := x.isLt
  have hy := y.isLt
  by_cases h : y.toNat ≤ x.toNat
  · exact Or.inl ⟨h, by rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr h)]; omega⟩
  · refine Or.inr ⟨by omega, ?_⟩
    rw [BitVec.toNat_sub_of_lt (BitVec.lt_def.mpr (by omega))]
    omega

theorem toNat_ofNat_toNat_bool (hw : 0 < w) (c : Bool) :
    (BitVec.ofNat w c.toNat).toNat = c.toNat := by
  rw [BitVec.toNat_ofNat]
  cases c
  · simp
  · exact Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))

/-- `x.bmod (2^w) = x` iff `x` is a representable signed `w`-bit value (`0 < w`). -/
theorem _root_.Int.bmod_two_pow_eq_self_iff (hw : 0 < w) (x : Int) :
    x.bmod (2 ^ w) = x ↔ -2 ^ (w - 1) ≤ x ∧ x < 2 ^ (w - 1) := by
  obtain ⟨w, rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  have h2 : (2 ^ (w + 1) : Nat) = 2 * 2 ^ w := by rw [Nat.pow_succ]; omega
  have hlo := Int.le_bmod (x := x) (m := 2 ^ (w + 1)) (Nat.two_pow_pos _)
  have hhi := Int.bmod_lt (x := x) (m := 2 ^ (w + 1)) (Nat.two_pow_pos _)
  simp only [Nat.add_one_sub_one]
  constructor
  · intro h
    rw [h] at hlo hhi
    push_cast [h2] at hlo hhi
    omega
  · rintro ⟨h1, h3⟩
    apply Int.bmod_eq_of_le
    · push_cast [h2]; omega
    · push_cast [h2]; omega

theorem toInt_ofNat_toNat_bool (hw : 1 < w) (c : Bool) :
    (BitVec.ofNat w c.toNat).toInt = c.toNat := by
  rw [BitVec.toInt_eq_toNat_bmod, BitVec.toNat_ofNat_toNat_bool (by omega)]
  have hn : 2 ≤ 2 ^ (w - 1) := Nat.one_lt_two_pow (by omega)
  have hi : (2 : Int) ≤ 2 ^ (w - 1) := by exact_mod_cast hn
  rw [(Int.bmod_two_pow_eq_self_iff (by omega) _).mpr]
  cases c <;> simp <;> omega

/-- Signed subtraction overflow as a decided range test. -/
theorem ssubOverflow_eq_decide (a b : BitVec w) :
    BitVec.ssubOverflow a b =
      decide (a.toInt - b.toInt < -2 ^ (w - 1) ∨ 2 ^ (w - 1) ≤ a.toInt - b.toInt) := by
  simp only [BitVec.ssubOverflow, ge_iff_le, Bool.decide_or, Bool.or_comm]

/-- Signed addition overflow as a decided range test. -/
theorem saddOverflow_eq_decide (a b : BitVec w) :
    BitVec.saddOverflow a b =
      decide (a.toInt + b.toInt < -2 ^ (w - 1) ∨ 2 ^ (w - 1) ≤ a.toInt + b.toInt) := by
  simp only [BitVec.saddOverflow, ge_iff_le, Bool.decide_or, Bool.or_comm]

/-- Unsigned addition carry-out: wrapped sum differs from exact sum iff `2^w ≤ a + b`. -/
theorem unsigned_add_bne (a b : BitVec w) :
    ((a + b).unsigned != a.unsigned + b.unsigned) = decide (2 ^ w ≤ a.toNat + b.toNat) := by
  rw [Bool.eq_iff_iff]
  simp only [BitVec.unsigned, bne_iff_ne, decide_eq_true_eq]
  have := BitVec.toNat_add_cases a b
  omega

/-- Signed addition overflow: wrapped signed sum differs from exact sum iff `saddOverflow a b`. -/
theorem signed_add_bne (a b : BitVec w) :
    ((a + b).signed != a.signed + b.signed) = BitVec.saddOverflow a b := by
  rw [BitVec.saddOverflow_eq_decide]
  rcases w with _ | w
  · simp [BitVec.signed, BitVec.of_length_zero]
  · rw [Bool.eq_iff_iff]
    simp only [BitVec.signed, bne_iff_ne, decide_eq_true_eq,
      BitVec.toInt_add, ne_eq, Int.bmod_two_pow_eq_self_iff (w := w + 1) (by omega)]
    omega

/-- Unsigned add-with-carry carry-out (`c : Bool`). -/
theorem unsigned_adc_bne (a b : BitVec w) (c : Bool) :
    ((a + b + BitVec.ofNat w c.toNat).unsigned !=
      a.unsigned + b.unsigned + (if c then 1 else 0)) =
      decide (2 ^ w ≤ a.toNat + b.toNat + c.toNat) := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · cases c <;> simp [BitVec.unsigned, BitVec.of_length_zero]
  rw [Bool.eq_iff_iff]
  simp only [BitVec.unsigned, bne_iff_ne, decide_eq_true_eq]
  have h1 := BitVec.toNat_add_cases a b
  have h2 := BitVec.toNat_add_cases (a + b) (BitVec.ofNat w c.toNat)
  rw [BitVec.toNat_ofNat_toNat_bool hw] at h2
  cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Bool.false_eq_true, ↓reduceIte]
    at h2 ⊢ <;> omega

/-- Unsigned add-with-carry carry-out with coerced `c : Bool`. -/
theorem unsigned_adc_bne_coe (a b : BitVec w) (c : Bool) :
    ((a + b + BitVec.ofNat w c.toNat).unsigned !=
      a.unsigned + b.unsigned + (c.toNat : Int)) =
      decide (2 ^ w ≤ a.toNat + b.toNat + c.toNat) := by
  rw [← unsigned_adc_bne a b c]
  cases c <;> rfl

/-- Signed add-with-carry overflow (`1 < w`). -/
theorem signed_adc_bne (a b : BitVec w) (c : Bool) (hw : 1 < w) :
    ((a + b + BitVec.ofNat w c.toNat).signed !=
      a.signed + b.signed + (if c then 1 else 0)) =
      decide (a.toInt + b.toInt + c.toNat < -2 ^ (w - 1) ∨
        2 ^ (w - 1) ≤ a.toInt + b.toInt + c.toNat) := by
  rw [Bool.eq_iff_iff]
  simp only [BitVec.signed, bne_iff_ne, decide_eq_true_eq, BitVec.toInt_add,
    Int.bmod_add_bmod, BitVec.toInt_ofNat_toNat_bool hw, ne_eq]
  cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Bool.false_eq_true, ↓reduceIte,
    Int.natCast_zero, Int.natCast_one, Int.add_zero,
    Int.bmod_two_pow_eq_self_iff (w := w) (by omega)] <;> omega

/-- Signed add-with-carry overflow with coerced `c : Bool` (`1 < w`). -/
theorem signed_adc_bne_coe (a b : BitVec w) (c : Bool) (hw : 1 < w) :
    ((a + b + BitVec.ofNat w c.toNat).signed !=
      a.signed + b.signed + (c.toNat : Int)) =
      decide (a.toInt + b.toInt + c.toNat < -2 ^ (w - 1) ∨
        2 ^ (w - 1) ≤ a.toInt + b.toInt + c.toNat) := by
  rw [← signed_adc_bne a b c hw]
  cases c <;> rfl

/-- Unsigned subtraction borrow (`!=`): wrapped difference differs from exact difference iff `a < b`. -/
theorem unsigned_sub_bne (a b : BitVec w) :
    ((a - b).unsigned != a.unsigned - b.unsigned) = decide (a.toNat < b.toNat) := by
  rw [Bool.eq_iff_iff]
  simp only [BitVec.unsigned, bne_iff_ne, decide_eq_true_eq]
  have := BitVec.toNat_sub_cases a b
  have := a.isLt; have := b.isLt
  omega

/-- Unsigned subtraction no-borrow (`==`): wrapped difference equals exact difference iff `b ≤ a`. -/
theorem unsigned_sub_beq (a b : BitVec w) :
    ((a - b).unsigned == a.unsigned - b.unsigned) = decide (b.toNat ≤ a.toNat) := by
  rw [Bool.eq_iff_iff]
  simp only [BitVec.unsigned, beq_iff_eq, decide_eq_true_eq]
  have := BitVec.toNat_sub_cases a b
  have := a.isLt; have := b.isLt
  omega

/-- Signed subtraction overflow: wrapped signed difference differs from exact difference iff `ssubOverflow a b`. -/
theorem signed_sub_bne (a b : BitVec w) :
    ((a - b).signed != a.signed - b.signed) = BitVec.ssubOverflow a b := by
  rw [BitVec.ssubOverflow_eq_decide]
  rcases w with _ | w
  · simp [BitVec.signed, BitVec.of_length_zero]
  · rw [Bool.eq_iff_iff]
    simp only [BitVec.signed, bne_iff_ne, decide_eq_true_eq,
      BitVec.toInt_sub, ne_eq, Int.bmod_two_pow_eq_self_iff (w := w + 1) (by omega)]
    omega

/-- Unsigned subtract-with-borrow borrow-out (`!=`, `c : Bool` is borrow-in). -/
theorem unsigned_sbb_bne (a b : BitVec w) (c : Bool) :
    ((a - b - BitVec.ofNat w c.toNat).unsigned !=
      a.unsigned - b.unsigned - (c.toNat : Int)) =
      decide (a.toNat < b.toNat + c.toNat) := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · cases c <;> simp [BitVec.unsigned, BitVec.of_length_zero]
  rw [Bool.eq_iff_iff]
  simp only [BitVec.unsigned, bne_iff_ne, decide_eq_true_eq]
  have h1 := BitVec.toNat_sub_cases a b
  have h2 := BitVec.toNat_sub_cases (a - b) (BitVec.ofNat w c.toNat)
  rw [BitVec.toNat_ofNat_toNat_bool hw] at h2
  have := a.isLt; have := b.isLt
  cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Int.natCast_zero, Int.natCast_one,
    Int.sub_zero] at h2 ⊢ <;> omega

/-- Unsigned subtract-with-carry no-borrow (`==`, `cin : Bool` is inverted borrow-in). -/
theorem unsigned_sbc_beq (a b : BitVec w) (cin : Bool) :
    ((a - b - BitVec.ofNat w (!cin).toNat).unsigned ==
      a.unsigned - b.unsigned - (if cin then 0 else 1)) =
      decide (b.toNat + (!cin).toNat ≤ a.toNat) := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · cases cin <;> simp [BitVec.unsigned, BitVec.of_length_zero]
  rw [Bool.eq_iff_iff]
  simp only [BitVec.unsigned, beq_iff_eq, decide_eq_true_eq]
  have h1 := BitVec.toNat_sub_cases a b
  have h2 := BitVec.toNat_sub_cases (a - b) (BitVec.ofNat w (!cin).toNat)
  rw [BitVec.toNat_ofNat_toNat_bool hw] at h2
  have := a.isLt; have := b.isLt
  cases cin <;> simp only [Bool.not_false, Bool.not_true, Bool.toNat_false, Bool.toNat_true,
    Bool.false_eq_true, ↓reduceIte] at h2 ⊢ <;> omega

/-- Signed subtract-with-borrow overflow (`1 < w`, `c : Bool` is borrow-in). -/
theorem signed_sbb_bne_coe (a b : BitVec w) (c : Bool) (hw : 1 < w) :
    ((a - b - BitVec.ofNat w c.toNat).signed !=
      a.signed - b.signed - (c.toNat : Int)) =
      decide (a.toInt - b.toInt - c.toNat < -2 ^ (w - 1) ∨
        2 ^ (w - 1) ≤ a.toInt - b.toInt - c.toNat) := by
  rw [Bool.eq_iff_iff]
  simp only [BitVec.signed, bne_iff_ne, decide_eq_true_eq, BitVec.toInt_sub,
    Int.bmod_sub_bmod, BitVec.toInt_ofNat_toNat_bool hw, ne_eq]
  cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Int.natCast_zero, Int.natCast_one,
    Int.sub_zero, Int.bmod_two_pow_eq_self_iff (w := w) (by omega)] <;> omega

/-- Signed subtract-with-carry overflow (`1 < w`, `cin : Bool` is inverted borrow-in). -/
theorem signed_sbc_bne (a b : BitVec w) (cin : Bool) (hw : 1 < w) :
    ((a - b - BitVec.ofNat w (!cin).toNat).signed !=
      a.signed - b.signed - (if cin then 0 else 1)) =
      decide (a.toInt - b.toInt - (!cin).toNat < -2 ^ (w - 1) ∨
        2 ^ (w - 1) ≤ a.toInt - b.toInt - (!cin).toNat) := by
  rw [← signed_sbb_bne_coe a b (!cin) hw]
  cases cin <;> rfl

/-- Wrapped sum plus carry-out weight equals exact sum. -/
theorem toNat_add_carry (a b : BitVec w) :
    ((a + b).toNat : Int) + (decide (2 ^ w ≤ a.toNat + b.toNat)).toNat * (2 ^ w : Nat) =
      a.toNat + b.toNat := by
  have := BitVec.toNat_add_cases a b
  by_cases h : 2 ^ w ≤ a.toNat + b.toNat <;> simp only [h, decide_true, decide_false,
    Bool.toNat_true, Bool.toNat_false] <;> omega

/-- Wrapped add-with-carry result plus carry-out weight equals exact sum. -/
theorem toNat_adc_carry (a b : BitVec w) (c : Bool) (hw : 0 < w) :
    ((a + b + BitVec.ofNat w c.toNat).toNat : Int) +
      (decide (2 ^ w ≤ a.toNat + b.toNat + c.toNat)).toNat * (2 ^ w : Nat) =
      a.toNat + b.toNat + c.toNat := by
  have h1 := BitVec.toNat_add_cases a b
  have h2 := BitVec.toNat_add_cases (a + b) (BitVec.ofNat w c.toNat)
  rw [BitVec.toNat_ofNat_toNat_bool hw] at h2
  have := a.isLt; have := b.isLt
  have hc : c.toNat ≤ 1 := by cases c <;> simp
  by_cases h : 2 ^ w ≤ a.toNat + b.toNat + c.toNat <;> simp only [h, decide_true, decide_false,
    Bool.toNat_true, Bool.toNat_false] <;> omega

/-- Wrapped difference minus borrow-out weight (`a < b`) equals exact difference. -/
theorem toNat_sub_borrow (a b : BitVec w) :
    ((a - b).toNat : Int) - (decide (a.toNat < b.toNat)).toNat * (2 ^ w : Nat) =
      a.toNat - b.toNat := by
  have := BitVec.toNat_sub_cases a b
  by_cases h : a.toNat < b.toNat <;> simp only [h, decide_true, decide_false,
    Bool.toNat_true, Bool.toNat_false] <;> omega

/-- Wrapped difference minus inverted-carry weight (`!(b ≤ a)`) equals exact difference. -/
theorem toNat_subs_carry (a b : BitVec w) :
    ((a - b).toNat : Int) - (!decide (b.toNat ≤ a.toNat)).toNat * (2 ^ w : Nat) =
      a.toNat - b.toNat := by
  have := BitVec.toNat_sub_cases a b
  by_cases h : b.toNat ≤ a.toNat <;> simp only [h, decide_true, decide_false, Bool.not_true,
    Bool.not_false, Bool.toNat_true, Bool.toNat_false] <;> omega

/-- Wrapped subtract-with-borrow result minus borrow-out weight equals exact difference. -/
theorem toNat_sbb_borrow (a b : BitVec w) (c : Bool) (hw : 0 < w) :
    ((a - b - BitVec.ofNat w c.toNat).toNat : Int) -
      (decide (a.toNat < b.toNat + c.toNat)).toNat * (2 ^ w : Nat) =
      a.toNat - b.toNat - c.toNat := by
  have h1 := BitVec.toNat_sub_cases a b
  have h2 := BitVec.toNat_sub_cases (a - b) (BitVec.ofNat w c.toNat)
  rw [BitVec.toNat_ofNat_toNat_bool hw] at h2
  have := a.isLt; have := b.isLt
  have hc : c.toNat ≤ 1 := by cases c <;> simp
  by_cases h : a.toNat < b.toNat + c.toNat <;> simp only [h, decide_true, decide_false,
    Bool.toNat_true, Bool.toNat_false] <;> omega

/-- Wrapped subtract-with-carry result minus inverted-carry weight equals exact difference. -/
theorem toNat_sbcs_carry (a b : BitVec w) (cin : Bool) (hw : 0 < w) :
    ((a - b - BitVec.ofNat w (!cin).toNat).toNat : Int) -
      (!decide (b.toNat + (!cin).toNat ≤ a.toNat)).toNat * (2 ^ w : Nat) =
      a.toNat - b.toNat - (!cin).toNat := by
  have h1 := BitVec.toNat_sub_cases a b
  have h2 := BitVec.toNat_sub_cases (a - b) (BitVec.ofNat w (!cin).toNat)
  rw [BitVec.toNat_ofNat_toNat_bool hw] at h2
  have := a.isLt; have := b.isLt
  have hc : (!cin).toNat ≤ 1 := by cases cin <;> simp
  by_cases h : b.toNat + (!cin).toNat ≤ a.toNat <;> simp only [h, decide_true, decide_false,
    Bool.not_true, Bool.not_false, Bool.toNat_true, Bool.toNat_false] <;> omega

section
variable (a b : BitVec w)

/-! ### The compare idiom: condition codes after `cmp a, b` (`subs`/`sub` flags)

A condition code unfolds to a `Bool` combination of the flag projections (`(subs a b).n != …`);
these `@[kcond]` lemmas fold the combinations back into one decided comparison
(`b.lo` ↦ `decide (a.toNat < b.toNat)`, `b.lt` ↦ `decide (a.toInt < b.toInt)`, …). They are
stated on the simp normal form of the projections, so they apply after them. -/

/-- `LT`: `n ≠ v` after `cmp a, b` is the signed comparison. -/
@[simp, kcond] theorem cmp_lt :
    ((a - b).msb != BitVec.ssubOverflow a b) = decide (a.toInt < b.toInt) := by
  rw [ssubOverflow_eq_decide]
  rcases w with _ | w
  · simp [BitVec.of_length_zero]
  · rw [Bool.eq_iff_iff]
    have h1 := BitVec.toInt_sub_toInt_lt_twoPow_iff (x := a) (y := b)
    have h2 := BitVec.twoPow_le_toInt_sub_toInt_iff (x := a) (y := b)
    have hself := Int.bmod_two_pow_eq_self_iff (w := w + 1) (by omega) (a.toInt - b.toInt)
    simp only [Nat.add_one_sub_one] at h1 h2 hself ⊢
    simp only [BitVec.msb_eq_toInt, BitVec.toInt_sub, bne_iff_ne, ne_eq, decide_eq_true_eq,
      decide_eq_decide]
    omega

/-- `GE`: `n = v` after `cmp a, b`. -/
@[simp, kcond] theorem cmp_ge :
    ((a - b).msb == BitVec.ssubOverflow a b) = decide (b.toInt ≤ a.toInt) := by
  rw [ssubOverflow_eq_decide]
  rcases w with _ | w
  · simp [BitVec.of_length_zero]
  · rw [Bool.eq_iff_iff]
    have h1 := BitVec.toInt_sub_toInt_lt_twoPow_iff (x := a) (y := b)
    have h2 := BitVec.twoPow_le_toInt_sub_toInt_iff (x := a) (y := b)
    have hself := Int.bmod_two_pow_eq_self_iff (w := w + 1) (by omega) (a.toInt - b.toInt)
    simp only [Nat.add_one_sub_one] at h1 h2 hself ⊢
    simp only [BitVec.msb_eq_toInt, BitVec.toInt_sub, beq_iff_eq, decide_eq_true_eq,
      decide_eq_decide]
    omega

/-- `GT`: `¬z ∧ n = v` after `cmp a, b` (stated on the simp normal form of the projections). -/
@[simp, kcond] theorem cmp_gt :
    (!decide (a = b) && decide (b.toInt ≤ a.toInt)) = decide (b.toInt < a.toInt) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
  constructor
  · rintro ⟨hne, hle⟩
    rcases Int.lt_or_eq_of_le hle with h | h
    · exact h
    · exact absurd (BitVec.toInt_inj.mp h.symm) hne
  · intro h
    exact ⟨fun heq => by subst heq; omega, Int.le_of_lt h⟩

/-- `LE`: `z ∨ n ≠ v` after `cmp a, b`. -/
@[simp, kcond] theorem cmp_le :
    (decide (a = b) || decide (a.toInt < b.toInt)) = decide (a.toInt ≤ b.toInt) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro (h | h)
    · subst h; omega
    · exact Int.le_of_lt h
  · intro h
    rcases Int.lt_or_eq_of_le h with h | h
    · exact Or.inr h
    · exact Or.inl (BitVec.toInt_inj.mp h)

/-- `HI`: `c ∧ ¬z` after `cmp a, b`. -/
@[simp, kcond] theorem cmp_hi :
    (decide (b.toNat ≤ a.toNat) && !decide (a = b)) = decide (b.toNat < a.toNat) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
    ← BitVec.toNat_inj]
  omega

/-- `LS`: `¬c ∨ z` after `cmp a, b`. -/
@[simp, kcond] theorem cmp_ls :
    (!decide (b.toNat ≤ a.toNat) || decide (a = b)) = decide (a.toNat ≤ b.toNat) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
    ← BitVec.toNat_inj]
  omega

/-- `BE`/`LS` with the borrow flag (`cf` after `cmp a, b` is `decide (a.toNat < b.toNat)`). -/
@[simp, kcond] theorem cmp_be :
    (decide (a.toNat < b.toNat) || decide (a = b)) = decide (a.toNat ≤ b.toNat) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq, ← BitVec.toNat_inj]
  omega

/-- `A`/`HI` with the borrow flag. -/
@[simp, kcond] theorem cmp_a :
    (!decide (a.toNat < b.toNat) && !decide (a = b)) = decide (b.toNat < a.toNat) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
    ← BitVec.toNat_inj]
  omega

/-- `LE` with the disjuncts in the `(sf != of) || zf` order. -/
@[simp, kcond] theorem cmp_le' :
    (decide (a.toInt < b.toInt) || decide (a = b)) = decide (a.toInt ≤ b.toInt) := by
  rw [Bool.or_comm]; exact cmp_le a b

end

/-- Stack-pointer alignment modulo 16 is invariant under adding a 16-byte-aligned offset. -/
@[kcond] theorem add_umod_16_right (a b : BitVec 64) (hb : b % 16#64 = 0#64) :
    (a + b) % 16#64 = a % 16#64 := by
  grind

@[kcond] theorem add_umod_16_left (a b : BitVec 64) (ha : a % 16#64 = 0#64) :
    (a + b) % 16#64 = b % 16#64 := by
  grind

end BitVec

/-! ### 64-bit word and multi-limb register helpers -/

export BitVec (shift256Word_lsb_or_clamped)

theorem or4_eq_zero_iff (x0 x1 x2 x3 : BitVec 64) :
    ((x0 ||| x1 ||| x2 ||| x3) = 0#64) ↔
      (x0 = 0#64 ∧ x1 = 0#64 ∧ x2 = 0#64 ∧ x3 = 0#64) := by
  grind

theorem or4_sub_one_eq_zero_iff (x0 x1 x2 x3 : BitVec 64) :
    ((x0 - 1#64 ||| x1 ||| x2 ||| x3) = 0#64) ↔
      (x0 = 1#64 ∧ x1 = 0#64 ∧ x2 = 0#64 ∧ x3 = 0#64) := by
  grind

theorem UInt64.getLsbD_zero_eq_false_mod2 (x : UInt64) (h : x.toBitVec.getLsbD 0 = false) :
    x.toNat % 2 = 0 := by
  simp only [BitVec.getLsbD, Nat.testBit_zero, decide_eq_false_iff_not] at h
  rw [← UInt64.toNat_toBitVec]
  omega

theorem UInt64.getLsbD_zero_eq_true_mod2 (x : UInt64) (h : x.toBitVec.getLsbD 0 = true) :
    x.toNat % 2 = 1 := by
  simp only [BitVec.getLsbD, Nat.testBit_zero, decide_eq_true_eq] at h
  rw [← UInt64.toNat_toBitVec]
  exact h

@[simp, grind =]
theorem UInt64.toNat_ofBitVec_ushiftRight_one (x : UInt64) :
    (UInt64.ofBitVec (x.toBitVec >>> 1)).toNat = x.toNat / 2 := by
  rw [UInt64.toNat_ofBitVec, BitVec.toNat_ushiftRight, UInt64.toNat_toBitVec, Nat.shiftRight_eq_div_pow]

@[simp, grind =]
theorem UInt64.toNat_ofBitVec_and_one (x : UInt64) :
    (UInt64.ofBitVec (x.toBitVec &&& 1#64)).toNat = x.toNat % 2 := by
  rw [UInt64.toNat_ofBitVec, BitVec.toNat_and, UInt64.toNat_toBitVec]
  exact Nat.and_one_is_mod x.toNat

theorem UInt64.ushiftRight_one_eq_zero_iff (x : UInt64) :
    (x.toBitVec >>> 1 = 0#64) ↔ x.toNat / 2 = 0 := by
  rw [← BitVec.toNat_inj, BitVec.toNat_ushiftRight, UInt64.toNat_toBitVec, Nat.shiftRight_eq_div_pow]
  rfl

theorem UInt64.and_one_eq_zero_iff (x : UInt64) :
    (x.toBitVec &&& 1#64 = 0#64) ↔ x.toNat % 2 = 0 := by
  rw [← BitVec.toNat_inj, BitVec.toNat_and, UInt64.toNat_toBitVec]
  exact Iff.of_eq (congrArg (· = 0) (Nat.and_one_is_mod x.toNat))

@[simp]
theorem UInt64.toNat_cset_cs (c : Bool) :
    ((UInt64.ofBitVec (if !c then 0#64 else 1#64) : UInt64).toNat : Int) = if c then 1 else 0 := by
  cases c <;> rfl

@[simp]
theorem UInt64.toNat_cset_cc (c : Bool) :
    ((UInt64.ofBitVec (if c then 0#64 else 1#64) : UInt64).toNat : Int) = if c then 0 else 1 := by
  cases c <;> rfl

theorem UInt64.toNat_cset_le_one (c : Bool) :
    (UInt64.ofBitVec (if c then 0#64 else 1#64) : UInt64).toNat ≤ 1 := by
  cases c <;> decide

theorem sub_one_beq_zero_false_of_gt_one (x : UInt64) (h : 1 < x.toNat) :
    ((x.toBitVec - 1#64) == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro h_eq
  have h_nat : (x.toBitVec - 1#64).toNat = 0 := congrArg BitVec.toNat h_eq
  rw [BitVec.toNat_sub_of_le] at h_nat
  · change x.toNat - 1 = 0 at h_nat; omega
  · rw [BitVec.le_def]; change 1 ≤ x.toNat; omega

theorem toNat_sub_one_of_pos (x : UInt64) (h : 0 < x.toNat) :
    (UInt64.ofBitVec (x.toBitVec - 1#64)).toNat = x.toNat - 1 := by
  rw [UInt64.toNat_ofBitVec, BitVec.toNat_sub_of_le]
  · rfl
  · rw [BitVec.le_def]; change 1 ≤ x.toNat; omega

/-- Single 64-bit limb produced by a 1-bit funnel right shift `(hi <<< 63) ||| (lo >>> 1)`. -/
def extr1Word (hi lo : UInt64) : BitVec 64 :=
  (hi.toBitVec <<< 63) ||| (lo.toBitVec >>> 1)

theorem extr_sem_eq (hi lo : UInt64) :
    hi.toBitVec <<< 63 ||| lo.toBitVec >>> 1 = extr1Word hi lo := rfl

theorem extr1Word_toNat (hi lo : UInt64) :
    (UInt64.ofBitVec (extr1Word hi lo)).toNat =
      lo.toNat / 2 + 2 ^ 63 * (hi.toNat % 2) := by
  dsimp only [extr1Word]
  rw [UInt64.toNat_ofBitVec, BitVec.or_comm,
    BitVec.toNat_funnel_nat' lo.toBitVec hi.toBitVec (k := 1) (m := 63) rfl,
    UInt64.toNat_toBitVec, UInt64.toNat_toBitVec]
  omega

/-- Clamped trailing-zero count `(w.reverse ||| 1).clz` in `[0, 63]`. -/
def ctzClamped (w : UInt64) : BitVec 64 :=
  (w.toBitVec.reverse ||| 1#64).clz

/-- Single 64-bit limb produced by a variable funnel right shift `(lo >> k) | (hi << (-k))`. -/
def shift256Word (lo hi : UInt64) (k : BitVec 64) : BitVec 64 :=
  lo.toBitVec.ushiftRight (k.toNat % 64) ||| (hi.toBitVec <<< ((0#64 - k).toNat % 64))

/-- Top 64-bit limb produced by a variable right shift `hi >> k`. -/
def shift256TopWord (hi : UInt64) (k : BitVec 64) : BitVec 64 :=
  hi.toBitVec.ushiftRight (k.toNat % 64)

theorem shift256Word_eq_aux (lo hi : UInt64) (k d : BitVec 64) :
    (lo.toBitVec.ushiftRight (k.toNat % 64) ||| (hi.toBitVec <<< (d.toNat % 64))) =
      (lo.toBitVec >>> (k % 64#64)) ||| (hi.toBitVec <<< (d % 64#64)) := by
  have h1 : (k % 64#64).toNat = k.toNat % 64 := BitVec.toNat_umod
  have h2 : (d % 64#64).toNat = d.toNat % 64 := BitVec.toNat_umod
  rw [← h1, ← h2]
  rfl

theorem shift256Word_eq (lo hi : UInt64) (k : BitVec 64) :
    shift256Word lo hi k =
      (lo.toBitVec >>> (k % 64#64)) ||| (hi.toBitVec <<< ((0#64 - k) % 64#64)) :=
  shift256Word_eq_aux lo hi k (0#64 - k)

theorem shift256TopWord_eq (hi : UInt64) (k : BitVec 64) :
    shift256TopWord hi k = hi.toBitVec >>> (k % 64#64) := by
  dsimp only [shift256TopWord]
  have h1 : (k % 64#64).toNat = k.toNat % 64 := BitVec.toNat_umod
  rw [← h1]
  rfl

theorem shift256_limb_toNat (lo hi : UInt64) (k : BitVec 64)
    (hk1 : 1#64 ≤ k) (hk63 : k ≤ 63#64) :
    let mask := (1#64 <<< (k % 64#64)) - 1#64
    2 ^ k.toNat * (UInt64.ofBitVec (shift256Word lo hi k)).toNat +
      (lo.toBitVec &&& mask).toNat =
      lo.toNat + 2 ^ 64 * (hi.toBitVec &&& mask).toNat := by
  dsimp only
  rw [UInt64.toNat_ofBitVec, shift256Word_eq]
  exact BitVec.toNat_funnel_mul_add_and_mask lo.toBitVec hi.toBitVec hk1 hk63

theorem shift256_top_toNat (hi : UInt64) (k : BitVec 64) (hk63 : k ≤ 63#64) :
    let mask := (1#64 <<< (k % 64#64)) - 1#64
    2 ^ k.toNat * (UInt64.ofBitVec (shift256TopWord hi k)).toNat +
      (hi.toBitVec &&& mask).toNat = hi.toNat := by
  dsimp only
  rw [UInt64.toNat_ofBitVec, shift256TopWord_eq]
  exact BitVec.toNat_ushiftRight_mul_add_and_mask hi.toBitVec hk63

/-! ### Integer power-of-two and odd-modulus lemmas -/

theorem odd_of_dvd_odd (c g : Int) (hg : g % 2 = 1) (h : c ∣ g) : c % 2 = 1 := by
  obtain ⟨q, rfl⟩ := h
  have h01 : c % 2 = 0 ∨ c % 2 = 1 := by omega
  rcases h01 with h0 | h1
  · rw [Int.mul_emod, h0, Int.zero_mul, Int.zero_emod] at hg
    omega
  · exact h1

theorem odd_dvd_of_dvd_two_mul (c m : Int) (hc : c % 2 = 1) (h : c ∣ 2 * m) : c ∣ m := by
  have h2 : (c + 1) / 2 * 2 = c + 1 :=
    Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero (by omega))
  have h_eq : m = (c + 1) / 2 * (2 * m) - c * m := by
    rw [← Int.mul_assoc, h2, Int.add_mul, Int.one_mul]
    omega
  rw [h_eq]
  exact Int.dvd_sub (Int.dvd_mul_of_dvd_right h) (Int.dvd_mul_right c m)

theorem odd_dvd_of_dvd_two_pow_mul (c : Int) (hc : c % 2 = 1) (k : Nat) (m : Int)
    (h : c ∣ ((2 ^ k : Nat) : Int) * m) : c ∣ m := by
  induction k generalizing m with
  | zero => simpa using h
  | succ k ih =>
    apply odd_dvd_of_dvd_two_mul c m hc
    apply ih
    have : ((2 ^ (k + 1) : Nat) : Int) * m = ((2 ^ k : Nat) : Int) * (2 * m) := by
      rw [Nat.pow_succ, Int.natCast_mul]; grind
    rw [← this]
    exact h

/-- Dividing `B` by a power of two preserves `gcd A B` when that gcd is odd. -/
theorem Int.gcd_of_two_pow_mul_odd (A B B' : Int) (k : Nat) (h : ((2 ^ k : Nat) : Int) * B' = B)
    (hodd : (Int.gcd A B : Int) % 2 = 1) : Int.gcd A B' = Int.gcd A B := by
  rw [Int.gcd_right_eq_iff]
  intro c hcA
  constructor
  · intro hcB'
    rw [← h]
    exact Int.dvd_mul_of_dvd_right hcB'
  · intro hcB
    have hcg : c ∣ (Int.gcd A B : Int) := Int.dvd_coe_gcd hcA hcB
    have hc_odd : c % 2 = 1 := odd_of_dvd_odd c _ hodd hcg
    exact odd_dvd_of_dvd_two_pow_mul c hc_odd k B' (h ▸ hcB)

theorem pow2_mul_bound_step (m : Nat) (x x' n z : Int)
    (h_inv : ((2 ^ m : Nat) : Int) * x ≤ z + (((2 ^ m : Nat) : Int) - 1) * n)
    (h_step : 2 * x' ≤ x + n) :
    ((2 ^ (m + 1) : Nat) : Int) * x' ≤ z + (((2 ^ (m + 1) : Nat) : Int) - 1) * n := by
  have h0 : (0 : Int) ≤ ((2 ^ m : Nat) : Int) := by exact_mod_cast Nat.zero_le _
  have h1 := Int.mul_le_mul_of_nonneg_left h_step h0
  have h_pow : ((2 ^ (m + 1) : Nat) : Int) = ((2 ^ m : Nat) : Int) * 2 := by
    rw [Nat.pow_succ, Int.natCast_mul]; rfl
  rw [h_pow]
  grind

theorem pow2_mul_emod_step (m : Nat) (x x' n z : Int)
    (h_inv : (((2 ^ m : Nat) : Int) * x) % n = z)
    (h_step : (2 * x') % n = x % n) :
    (((2 ^ (m + 1) : Nat) : Int) * x') % n = z := by
  have h_pow : ((2 ^ (m + 1) : Nat) : Int) * x' = ((2 ^ m : Nat) : Int) * (2 * x') := by
    rw [Nat.pow_succ, Int.natCast_mul]; grind
  rw [h_pow, Int.mul_emod, h_step, ← Int.mul_emod, h_inv]

theorem two_mul_emod_eq_zero_of_odd (z n : Int) (hn_odd : n % 2 = 1)
    (h : (2 * z) % n = 0) : z % n = 0 := by
  obtain ⟨q, hq⟩ : n ∣ 2 * z := Int.dvd_of_emod_eq_zero h
  have hn_eq : n = 2 * (n / 2) + 1 := by omega
  have hz : z = n * (z - (n / 2) * q) + (2 * z - n * q) * (n / 2) := by grind
  have h2z : 2 * z - n * q = 0 := by omega
  rw [h2z, Int.zero_mul, Int.add_zero] at hz
  exact Int.emod_eq_zero_of_dvd ⟨z - (n / 2) * q, hz⟩

theorem pow2_mul_emod_eq_zero_of_odd (k : Nat) (z n : Int) (hn_odd : n % 2 = 1)
    (h : (((2 ^ k : Nat) : Int) * z) % n = 0) : z % n = 0 := by
  induction k generalizing z with
  | zero =>
    simp only [Nat.pow_zero, Int.natCast_one, Int.one_mul] at h
    exact h
  | succ k ih =>
    apply ih z
    apply two_mul_emod_eq_zero_of_odd (((2 ^ k : Nat) : Int) * z) n hn_odd
    have h_eq : 2 * (((2 ^ k : Nat) : Int) * z) = ((2 ^ (k + 1) : Nat) : Int) * z := by
      rw [Nat.pow_succ, Int.natCast_mul]; grind
    rw [h_eq]
    exact h

theorem pos_and_le_of_pow2_mul (k : Nat) (b b' : Int)
    (hb_pos : 0 < b) (hb'_nonneg : 0 ≤ b')
    (h_eq : ((2 ^ k : Nat) : Int) * b' = b) :
    0 < b' ∧ b' ≤ b := by
  have h_pow_nat : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
  have h_pow_pos : (1 : Int) ≤ ((2 ^ k : Nat) : Int) := by omega
  have hb'_pos : 0 < b' := by
    rcases Int.lt_trichotomy 0 b' with h_pos | h_zero | h_neg
    · exact h_pos
    · rw [← h_zero, Int.mul_zero] at h_eq; omega
    · omega
  have hb'_le : b' ≤ b := by
    have : 1 * b' ≤ ((2 ^ k : Nat) : Int) * b' :=
      Int.mul_le_mul_of_nonneg_right h_pow_pos hb'_nonneg
    omega
  exact ⟨hb'_pos, hb'_le⟩

end
