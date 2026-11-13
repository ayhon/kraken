module

/-!
# Little-Endian Byte Conversion (`toBytes` / `ofBytes`)

Conversions between integers, natural numbers, fixed-width machine words (`BitVec`, `UInt8`,
`UInt16`, `UInt32`, `UInt64`), and little-endian byte lists (`List UInt8`), together with
roundtrip, slicing, and byte-list comparison lemmas.
-/

@[expose] public section

/-! ### Definitions and basic length properties -/

abbrev Nat.take (v : Nat) (w : Nat) : Nat := v % 2 ^ w
abbrev Int.take (v : Int) (w : Nat) : Int := v % (2 : Int) ^ w

instance : Coe UInt8 (BitVec 8) := ⟨UInt8.toBitVec⟩
instance : Coe UInt16 (BitVec 16) := ⟨UInt16.toBitVec⟩
instance : Coe UInt32 (BitVec 32) := ⟨UInt32.toBitVec⟩
instance : Coe UInt64 (BitVec 64) := ⟨UInt64.toBitVec⟩

/-- Little-endian unsigned value of a byte list as an `Int`. -/
def Int.ofBytes (bs : List UInt8) : Int :=
  bs.foldr (fun b acc => acc * 256 + b.toNat) 0

/-- Little-endian unsigned value of a byte list as a `Nat`. -/
def Nat.ofBytes (bs : List UInt8) : Nat :=
  bs.foldr (fun b acc => acc * 256 + b.toNat) 0

/-- Little-endian `n`-byte representation of `v : Int`. -/
def Int.toBytes (n : Nat) (v : Int) : List UInt8 :=
  match n with
  | 0 => []
  | n' + 1 => ((v.take 8).toNat.toUInt8) :: Int.toBytes n' (v / 256)

@[simp, grind =]
theorem Int.toBytes_length (n : Nat) (v : Int) : (Int.toBytes n v).length = n := by
  induction n generalizing v <;> simp [Int.toBytes, *]

@[simp, grind =]
theorem Int.toBytes_zero (n : Nat) : Int.toBytes n 0 = List.replicate n 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Int.toBytes, Int.take, ih]; rfl

/-- Little-endian `n`-byte representation of `v : Nat`. -/
def Nat.toBytes (n : Nat) (v : Nat) : List UInt8 :=
  match n with
  | 0 => []
  | n' + 1 => (v.take 8).toUInt8 :: Nat.toBytes n' (v / 256)

@[simp, grind =]
theorem Nat.toBytes_length (n : Nat) (v : Nat) : (Nat.toBytes n v).length = n := by
  induction n generalizing v <;> simp [Nat.toBytes, *]

/-! ### `Int.ofBytes` and `Int.toBytes` roundtrip and slicing lemmas -/

private theorem emod_mul_add_div_helper (d M K RQ RV : Int) :
    d * (M * K + RQ) + RV = RQ * d + RV + (M * d) * K := by
  rw [Int.mul_add]
  ac_rfl

private theorem emod_mul_add_div (v M d : Int) (hM : M > 0) (hd : d > 0) :
    ((v / d) % M) * d + v % d = v % (M * d) := by
  have h_vd : v / d = M * ((v / d) / M) + (v / d) % M := (Int.mul_ediv_add_emod (v / d) M).symm
  have h_v : v = d * (v / d) + v % d := (Int.mul_ediv_add_emod v d).symm
  rw [h_vd, emod_mul_add_div_helper] at h_v
  conv => rhs; rw [h_v, Int.add_mul_emod_self_left]
  have h_nn : 0 ≤ ((v / d) % M) * d + v % d :=
    Int.add_nonneg (Int.mul_nonneg (Int.emod_nonneg _ (by omega)) (by omega)) (Int.emod_nonneg _ (by omega))
  have h_lt : ((v / d) % M) * d + v % d < M * d := by
    have h := Int.mul_le_mul_of_nonneg_right
      (show (v / d) % M ≤ M - 1 by have := Int.emod_lt_of_pos (v / d) hM; omega) (show 0 ≤ d by omega)
    have := Int.emod_lt_of_pos v hd
    rw [Int.sub_mul, Int.one_mul] at h
    omega
  exact (Int.emod_eq_of_lt h_nn h_lt).symm

private theorem emod_div_mul (x M d : Int) (hM : M > 0) (hd : d > 0) :
    (x % (M * d)) / d = (x / d) % M := by
  have h_eq : x = x % (M * d) + (M * d) * (x / (M * d)) := by
    have := Int.mul_ediv_add_emod x (M * d); omega
  have h_div : x / d = (x % (M * d)) / d + M * (x / (M * d)) := by
    have h_mul : (M * d) * (x / (M * d)) = (M * (x / (M * d))) * d := by ac_rfl
    have h_eq' := h_eq
    rw [h_mul] at h_eq'
    rw [congrArg (· / d) h_eq']
    exact Int.add_mul_ediv_right _ _ (by omega)
  have h_mod_eq : (x / d) % M = ((x % (M * d)) / d) % M := by
    rw [h_div, Int.add_mul_emod_self_left]
  symm
  rw [h_mod_eq]
  have hMd : 0 < M * d := Int.mul_pos hM hd
  apply Int.emod_eq_of_lt
  · rw [Int.ediv_nonneg_iff_of_pos hd]
    exact Int.emod_nonneg _ (by omega)
  · have h_lt := Int.emod_lt x (show M * d ≠ 0 by omega)
    rw [Int.natAbs_of_nonneg (by omega)] at h_lt
    exact Int.ediv_lt_of_lt_mul hd h_lt

private theorem pow_256_eq_pow_2 (n w : Nat) (h : w = 8 * n) : (256 : Int) ^ n = (2 : Int) ^ w := by
  subst w
  rw [show (256 : Int) = 2 ^ 8 by decide, ← Int.pow_mul]

theorem Int.ofBytes_cons (b : UInt8) (bs : List UInt8) :
    Int.ofBytes (b :: bs) = Int.ofBytes bs * 256 + b.toNat := rfl

theorem Int.ofBytes_ge_zero (bs : List UInt8) : 0 ≤ Int.ofBytes bs := by
  induction bs with
  | nil => decide
  | cons b bs ih => simp [Int.ofBytes_cons]; omega

theorem Int.ofBytes_lt (bs : List UInt8) : Int.ofBytes bs < 256 ^ bs.length := by
  induction bs with
  | nil => decide
  | cons b bs ih =>
    simp [Int.ofBytes_cons, Int.pow_succ]
    have := Int.ofBytes_ge_zero bs
    dsimp [UInt8.toNat]
    omega

theorem Int.ofBytes_append (l1 l2 : List UInt8) :
    Int.ofBytes (l1 ++ l2) = Int.ofBytes l1 + 256 ^ l1.length * Int.ofBytes l2 := by
  induction l1 with
  | nil => simp [Int.ofBytes]
  | cons b l1 ih =>
    simp [Int.ofBytes_cons, ih, Int.pow_succ]
    rw [show 256 ^ l1.length * 256 * Int.ofBytes l2 = 256 ^ l1.length * Int.ofBytes l2 * 256 by ac_rfl]
    omega

theorem Int.ofBytes_take_drop_pair (bs : List UInt8) (n : Nat) (h : n ≤ bs.length) :
    Int.ofBytes bs = Int.ofBytes (bs.take n) + 256 ^ n * Int.ofBytes (bs.drop n) := by
  conv => lhs; rw [← List.take_append_drop n bs]
  rw [Int.ofBytes_append, List.length_take_of_le h]

theorem Int.ofBytes_take_add (bs : List UInt8) (m n : Nat) (h : m + n ≤ bs.length) :
    Int.ofBytes (bs.take (m + n)) =
      Int.ofBytes (bs.take m) + 256 ^ m * Int.ofBytes ((bs.drop m).take n) := by
  rw [List.take_add, Int.ofBytes_append, List.length_take_of_le (by omega)]

theorem Int.ofBytes_32_split (bs : List UInt8) (h : bs.length = 32) :
    Int.ofBytes bs =
      Int.ofBytes (bs.take 8) +
      256 ^ 8 * Int.ofBytes ((bs.drop 8).take 8) +
      256 ^ 16 * Int.ofBytes ((bs.drop 16).take 8) +
      256 ^ 24 * Int.ofBytes ((bs.drop 24).take 8) := by
  rw [Int.ofBytes_take_drop_pair bs 8 (by omega),
      Int.ofBytes_take_drop_pair (bs.drop 8) 8 (by simp [h]),
      List.drop_drop,
      Int.ofBytes_take_drop_pair (bs.drop 16) 8 (by simp [h]),
      List.drop_drop,
      show 16 + 8 = 24 by rfl,
      List.take_of_length_le (l := bs.drop 24) (i := 8) (by simp [h])]
  omega

theorem ofBytes_toBytes (n : Nat) (v : Int) : Int.ofBytes (Int.toBytes n v) = v.take (8 * n) := by
  induction n generalizing v with
  | zero =>
    simp [Int.toBytes, Int.ofBytes, Int.take]
  | succ n ih =>
    simp [Int.toBytes, Int.ofBytes_cons]
    rw [ih]
    simp [Int.take]
    have h_eq : max (v % 256) 0 % 256 = v % 256 := by omega
    rw [h_eq]
    have h_pow : (2 : Int) ^ (8 * (n + 1)) = (2 : Int) ^ (8 * n) * 256 := by
      rw [show 8 * (n + 1) = 8 * n + 8 by omega, Int.pow_add]; rfl
    rw [h_pow]
    exact emod_mul_add_div v _ 256 (Int.pow_pos (by decide)) (by omega)

theorem Int.toBytes_emod (n : Nat) (x : Int) : Int.toBytes n (x.take (8 * n)) = Int.toBytes n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [Int.toBytes, Int.take]
    have h_pow : (2 : Int) ^ (8 * (n + 1)) = (2 : Int) ^ (8 * n) * 256 := by
      rw [show 8 * (n + 1) = 8 * n + 8 by omega, Int.pow_add]; rfl
    rw [h_pow]
    have h_mod : (x % ((2 : Int) ^ (8 * n) * 256)) % 2 ^ 8 = x % 2 ^ 8 := by
      show (x % ((2 : Int) ^ (8 * n) * 256)) % 256 = x % 256
      apply Int.emod_emod_of_dvd
      rw [Int.mul_comm]
      exact ⟨(2 : Int) ^ (8 * n), rfl⟩
    have h_div : (x % ((2 : Int) ^ (8 * n) * 256)) / 256 = (x / 256) % (2 : Int) ^ (8 * n) :=
      emod_div_mul x _ 256 (Int.pow_pos (by decide)) (by decide)
    rw [h_mod, h_div, ih (x / 256)]

theorem Int.toBytes_ofBytes (n : Nat) (bs : List UInt8) (h : n ≤ bs.length) :
    Int.toBytes n (Int.ofBytes bs) = bs.take n := by
  induction n generalizing bs with
  | zero => rfl
  | succ n ih =>
    cases bs with
    | nil => contradiction
    | cons b bs =>
      cases b with | ofBitVec val =>
      simp only [Int.toBytes, Int.ofBytes_cons, List.take_succ_cons, UInt8.toNat]
      have h_lt : val.toNat < 256 := val.isLt
      have h_div : (Int.ofBytes bs * 256 + val.toNat) / 256 = Int.ofBytes bs := by omega
      have h_take : ((Int.ofBytes bs * 256 + val.toNat).take 8).toNat = val.toNat := by
        dsimp [Int.take]; omega
      simp only [List.length_cons] at h
      simp [h_div, h_take, ih bs (by omega)]

theorem Int.toBytes_ofBytes_all (bs : List UInt8) :
    Int.toBytes bs.length (Int.ofBytes bs) = bs := by
  rw [Int.toBytes_ofBytes bs.length bs (Nat.le_refl _), List.take_length]

theorem Int.toBytes_bmod_ofBytes (n : Nat) (bs : List UInt8) (h : bs.length = n) :
    Int.toBytes n ((Int.ofBytes bs).bmod (256 ^ n)) = bs := by
  subst h
  conv => rhs; rw [← Int.toBytes_ofBytes_all bs]
  rw [← Int.toBytes_emod bs.length ((Int.ofBytes bs).bmod (256 ^ bs.length)),
      ← Int.toBytes_emod bs.length (Int.ofBytes bs)]
  congr 1
  unfold Int.bmod
  dsimp
  have h_pow : (256 : Int) ^ bs.length = (2 : Int) ^ (8 * bs.length) :=
    pow_256_eq_pow_2 bs.length (8 * bs.length) rfl
  split
  · simp only [Int.take, h_pow, Int.emod_emod]
  · rw [show ofBytes bs % 256 ^ bs.length - 256 ^ bs.length =
        ofBytes bs % 256 ^ bs.length + 256 ^ bs.length * -1 by omega]
    simp only [Int.take, h_pow, Int.add_mul_emod_self_left, Int.emod_emod]

/-! ### `Nat.ofBytes` and `Nat.toBytes` roundtrip lemmas -/

private theorem Nat.mod_mul_add_div (v M d : Nat) :
    ((v / d) % M) * d + v % d = v % (M * d) := by
  rw [Nat.mul_comm M d, Nat.mod_mul, Nat.add_comm, Nat.mul_comm]

theorem Nat.ofBytes_cons (b : UInt8) (bs : List UInt8) :
    Nat.ofBytes (b :: bs) = Nat.ofBytes bs * 256 + b.toNat := rfl

theorem Nat.ofBytes_toBytes (n : Nat) (v : Nat) : Nat.ofBytes (Nat.toBytes n v) = v.take (8 * n) := by
  induction n generalizing v with
  | zero => simp [Nat.toBytes, Nat.ofBytes, Nat.take]; omega
  | succ n ih =>
    simp [Nat.toBytes, Nat.ofBytes_cons, ih, Nat.take]
    rw [show 2 ^ (8 * (n + 1)) = 2 ^ (8 * n) * 256 by
      rw [show 8 * (n + 1) = 8 * n + 8 by omega, Nat.pow_add]]
    exact Nat.mod_mul_add_div v (2 ^ (8 * n)) 256

theorem Nat.toBytes_ofBytes (n : Nat) (bs : List UInt8) (h : n ≤ bs.length) :
    Nat.toBytes n (Nat.ofBytes bs) = bs.take n := by
  induction n generalizing bs with
  | zero => rfl
  | succ n ih =>
    cases bs with
    | nil => contradiction
    | cons b bs =>
      cases b with | ofBitVec val =>
      simp only [Nat.toBytes, Nat.ofBytes_cons, List.take_succ_cons, UInt8.toNat]
      have h_div : (Nat.ofBytes bs * 256 + val.toNat) / 256 = Nat.ofBytes bs := by omega
      have h_mod : (Nat.ofBytes bs * 256 + val.toNat).take 8 = val.toNat := by
        dsimp [Nat.take]; omega
      rw [h_div, h_mod]
      simp only [List.length_cons] at h
      simp [ih bs (by omega)]

/-! ### `BitVec` and `UInt*` byte conversion lemmas -/

private theorem BitVec.ofInt_emod_self (w : Nat) (i : Int) :
    BitVec.ofInt w (i % (2 : Int) ^ w) = BitVec.ofInt w i := by
  simp [BitVec.ofInt]

theorem BitVec.ofInt_ofBytes_toBytes (w n : Nat) (h_wn : w = 8 * n) (val : BitVec w) :
    BitVec.ofInt w (Int.ofBytes (Int.toBytes n val.toInt)) = val := by
  rw [ofBytes_toBytes, show 8 * n = w from h_wn.symm, Int.take, BitVec.ofInt_emod_self]
  exact BitVec.ofInt_toInt

@[simp, grind =]
theorem BitVec.ofInt_ofBytes_toBytes_8 (val : BitVec 8) :
    BitVec.ofInt 8 (Int.ofBytes (Int.toBytes 1 val.toInt)) = val :=
  BitVec.ofInt_ofBytes_toBytes 8 1 rfl val

@[simp, grind =]
theorem BitVec.ofInt_ofBytes_toBytes_16 (val : BitVec 16) :
    BitVec.ofInt 16 (Int.ofBytes (Int.toBytes 2 val.toInt)) = val :=
  BitVec.ofInt_ofBytes_toBytes 16 2 rfl val

@[simp, grind =]
theorem BitVec.ofInt_ofBytes_toBytes_32 (val : BitVec 32) :
    BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 val.toInt)) = val :=
  BitVec.ofInt_ofBytes_toBytes 32 4 rfl val

@[simp, grind =]
theorem BitVec.ofInt_ofBytes_toBytes_64 (val : BitVec 64) :
    BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 val.toInt)) = val :=
  BitVec.ofInt_ofBytes_toBytes 64 8 rfl val

@[simp, grind =]
theorem BitVec.ofInt_ofBytes_singleton (x : UInt8) :
    BitVec.ofInt 8 (Int.ofBytes [x]) = x.toBitVec := by
  simp [Int.ofBytes]

theorem BitVec.ofInt_ofBytes_take (w n : Nat) (h_wn : w = 8 * n) (bs : List UInt8) :
    BitVec.ofInt w (Int.ofBytes bs) = BitVec.ofInt w (Int.ofBytes (bs.take n)) := by
  conv => lhs; rw [show bs = bs.take n ++ bs.drop n from (List.take_append_drop n bs).symm]
  rw [Int.ofBytes_append]
  by_cases hn : bs.length < n
  · rw [show bs.drop n = [] by apply List.drop_eq_nil_of_le; omega]
    simp [Int.ofBytes]
  · rw [show (bs.take n).length = n by apply List.length_take_of_le; omega]
    rw [pow_256_eq_pow_2 n w h_wn, BitVec.ofInt_add, BitVec.ofInt_mul]
    rw [show BitVec.ofInt w (2 ^ w) = 0#w by apply BitVec.eq_of_toNat_eq; simp]
    simp

theorem BitVec.toBytes_ofBytes (w n : Nat) (h_wn : w = 8 * n)
    (bs : List UInt8) (h : n ≤ bs.length) :
    Int.toBytes n (BitVec.ofInt w (Int.ofBytes bs)).toInt = bs.take n := by
  rw [BitVec.ofInt_ofBytes_take w n h_wn, BitVec.toInt_ofInt]
  rw [show 2 ^ w = 256 ^ n by
    subst w
    rw [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul]]
  exact Int.toBytes_bmod_ofBytes n (bs.take n) (List.length_take_of_le h)

theorem BitVec.toBytes_ofBytes_eq (w n : Nat) (h_wn : w = 8 * n)
    (bs : List UInt8) (h : bs.length = n) :
    Int.toBytes n (BitVec.ofInt w (Int.ofBytes bs)).toInt = bs := by
  rw [BitVec.toBytes_ofBytes w n h_wn bs (by omega), List.take_of_length_le (by omega)]

@[simp, grind =]
theorem BitVec.toBytes_ofBytes_8 (bs : List UInt8) (h : 1 ≤ bs.length) :
    Int.toBytes 1 (BitVec.ofInt 8 (Int.ofBytes bs)).toInt = bs.take 1 :=
  BitVec.toBytes_ofBytes 8 1 rfl bs h

@[simp, grind =]
theorem BitVec.toBytes_ofBytes_16 (bs : List UInt8) (h : 2 ≤ bs.length) :
    Int.toBytes 2 (BitVec.ofInt 16 (Int.ofBytes bs)).toInt = bs.take 2 :=
  BitVec.toBytes_ofBytes 16 2 rfl bs h

@[simp, grind =]
theorem BitVec.toBytes_ofBytes_32 (bs : List UInt8) (h : 4 ≤ bs.length) :
    Int.toBytes 4 (BitVec.ofInt 32 (Int.ofBytes bs)).toInt = bs.take 4 :=
  BitVec.toBytes_ofBytes 32 4 rfl bs h

@[simp, grind =]
theorem BitVec.toBytes_ofBytes_64 (bs : List UInt8) (h : 8 ≤ bs.length) :
    Int.toBytes 8 (BitVec.ofInt 64 (Int.ofBytes bs)).toInt = bs.take 8 :=
  BitVec.toBytes_ofBytes 64 8 rfl bs h

theorem Int.ofBytes_toNat_ofInt (w n : Nat) (h_wn : w = 8 * n)
    (bs : List UInt8) (h : bs.length = n) :
    ((BitVec.ofInt w (Int.ofBytes bs)).toNat : Int) = Int.ofBytes bs := by
  have h_ge : 0 ≤ Int.ofBytes bs := Int.ofBytes_ge_zero bs
  have h_lt : Int.ofBytes bs < (2 : Int) ^ w := by
    rw [← pow_256_eq_pow_2 n w h_wn, ← h]
    exact Int.ofBytes_lt bs
  have h_eq : BitVec.ofInt w (Int.ofBytes bs) = BitVec.ofNat w (Int.ofBytes bs).toNat := by
    rw [← BitVec.ofInt_natCast, Int.toNat_of_nonneg h_ge]
  have h_lt_nat : (Int.ofBytes bs).toNat < 2 ^ w := by
    rw [← Int.ofNat_lt, Int.toNat_of_nonneg h_ge]
    exact_mod_cast h_lt
  rw [h_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_lt_nat, Int.toNat_of_nonneg h_ge]

theorem Int.ofBytes_toNat_ofInt_64 (bs : List UInt8) (h : bs.length = 8) :
    ((BitVec.ofInt 64 (Int.ofBytes bs)).toNat : Int) = Int.ofBytes bs :=
  Int.ofBytes_toNat_ofInt 64 8 rfl bs h

theorem Int.ofBytes_toBytes_toInt (w n : Nat) (h_wn : w = 8 * n) (v : BitVec w) :
    Int.ofBytes (Int.toBytes n v.toInt) = (v.toNat : Int) := by
  rw [ofBytes_toBytes n v.toInt, ← h_wn]
  have h_lt : (v.toNat : Int) < (2 : Int) ^ w := by exact_mod_cast v.isLt
  have h_mod : (v.toNat : Int) % (2 : Int) ^ w = v.toNat :=
    Int.emod_eq_of_lt (Int.natCast_nonneg _) h_lt
  dsimp [Int.take, BitVec.toInt]
  split
  · exact h_mod
  · rw [show (v.toNat : Int) - (2 : Int) ^ w = (v.toNat : Int) + (2 : Int) ^ w * (-1) by omega,
        Int.add_mul_emod_self_left, h_mod]

@[simp, grind =]
theorem Int.ofBytes_toBytes_8_toInt (v : BitVec 64) :
    Int.ofBytes (Int.toBytes 8 v.toInt) = (v.toNat : Int) :=
  Int.ofBytes_toBytes_toInt 64 8 rfl v

def UInt8.toBytes (val : UInt8) : List UInt8 :=
  Int.toBytes 1 val.toBitVec.toInt

@[simp, grind =]
theorem UInt8.toBytes_length (val : UInt8) : val.toBytes.length = 1 := by
  simp [toBytes, Int.toBytes_length]

def UInt8.ofBytes (bs : List UInt8) : UInt8 :=
  ⟨BitVec.ofInt 8 (Int.ofBytes bs)⟩

theorem UInt8.ofBytes_toBytes (val : UInt8) : UInt8.ofBytes val.toBytes = val :=
  congrArg UInt8.ofBitVec (BitVec.ofInt_ofBytes_toBytes 8 1 rfl val.toBitVec)

@[simp, grind =]
theorem BitVec.ofInt_ofBytes_uInt8ToBytes (val : UInt8) :
    BitVec.ofInt 8 (Int.ofBytes val.toBytes) = val.toBitVec :=
  BitVec.ofInt_ofBytes_toBytes_8 val.toBitVec

theorem UInt8.toBytes_ofBytes (bs : List UInt8) (h : 1 ≤ bs.length) :
    (UInt8.ofBytes bs).toBytes = bs.take 1 :=
  BitVec.toBytes_ofBytes 8 1 rfl bs h

def UInt16.toBytes (val : UInt16) : List UInt8 :=
  Int.toBytes 2 val.toBitVec.toInt

@[simp, grind =]
theorem UInt16.toBytes_length (val : UInt16) : val.toBytes.length = 2 := by
  simp [toBytes, Int.toBytes_length]

def UInt16.ofBytes (bs : List UInt8) : UInt16 :=
  ⟨BitVec.ofInt 16 (Int.ofBytes bs)⟩

theorem UInt16.ofBytes_toBytes (val : UInt16) : UInt16.ofBytes val.toBytes = val :=
  congrArg UInt16.ofBitVec (BitVec.ofInt_ofBytes_toBytes 16 2 rfl val.toBitVec)

@[simp, grind =]
theorem BitVec.ofInt_ofBytes_uInt16ToBytes (val : UInt16) :
    BitVec.ofInt 16 (Int.ofBytes val.toBytes) = val.toBitVec :=
  BitVec.ofInt_ofBytes_toBytes_16 val.toBitVec

theorem UInt16.toBytes_ofBytes (bs : List UInt8) (h : 2 ≤ bs.length) :
    (UInt16.ofBytes bs).toBytes = bs.take 2 :=
  BitVec.toBytes_ofBytes 16 2 rfl bs h

def UInt32.toBytes (val : UInt32) : List UInt8 :=
  Int.toBytes 4 val.toBitVec.toInt

@[simp, grind =]
theorem UInt32.toBytes_length (val : UInt32) : val.toBytes.length = 4 := by
  simp [toBytes, Int.toBytes_length]

def UInt32.ofBytes (bs : List UInt8) : UInt32 :=
  ⟨BitVec.ofInt 32 (Int.ofBytes bs)⟩

theorem UInt32.ofBytes_toBytes (val : UInt32) : UInt32.ofBytes val.toBytes = val :=
  congrArg UInt32.ofBitVec (BitVec.ofInt_ofBytes_toBytes 32 4 rfl val.toBitVec)

@[simp, grind =]
theorem BitVec.ofInt_ofBytes_uInt32ToBytes (val : UInt32) :
    BitVec.ofInt 32 (Int.ofBytes val.toBytes) = val.toBitVec :=
  BitVec.ofInt_ofBytes_toBytes_32 val.toBitVec

theorem UInt32.toBytes_ofBytes (bs : List UInt8) (h : 4 ≤ bs.length) :
    (UInt32.ofBytes bs).toBytes = bs.take 4 :=
  BitVec.toBytes_ofBytes 32 4 rfl bs h

def UInt64.toBytes (val : UInt64) : List UInt8 :=
  Int.toBytes 8 val.toBitVec.toInt

@[simp, grind =]
theorem UInt64.toBytes_length (val : UInt64) : val.toBytes.length = 8 := by
  simp [toBytes, Int.toBytes_length]

def UInt64.ofBytes (bs : List UInt8) : UInt64 :=
  ⟨BitVec.ofInt 64 (Int.ofBytes bs)⟩

theorem UInt64.ofBytes_toBytes (val : UInt64) : UInt64.ofBytes val.toBytes = val :=
  congrArg UInt64.ofBitVec (BitVec.ofInt_ofBytes_toBytes 64 8 rfl val.toBitVec)

@[simp, grind =]
theorem BitVec.ofInt_ofBytes_uInt64ToBytes (val : UInt64) :
    BitVec.ofInt 64 (Int.ofBytes val.toBytes) = val.toBitVec :=
  BitVec.ofInt_ofBytes_toBytes_64 val.toBitVec

theorem UInt64.toBytes_ofBytes (bs : List UInt8) (h : 8 ≤ bs.length) :
    (UInt64.ofBytes bs).toBytes = bs.take 8 :=
  BitVec.toBytes_ofBytes 64 8 rfl bs h

/-! ### Byte-list XOR difference accumulator (`diffAcc`) -/

/-- Bitwise OR of all byte-wise XOR differences between `a` and `b`, zero-extended to 64 bits. -/
def diffAcc : List UInt8 → List UInt8 → BitVec 64
  | x :: xs, y :: ys => (x.toBitVec.setWidth 64 ^^^ y.toBitVec.setWidth 64) ||| diffAcc xs ys
  | _, _ => 0#64

@[simp]
theorem diffAcc_nil_left (b : List UInt8) : diffAcc [] b = 0#64 := rfl

@[simp]
theorem diffAcc_nil_right (a : List UInt8) : diffAcc a [] = 0#64 := by
  cases a <;> rfl

theorem diffAcc_eq_zero_iff (a b : List UInt8) (h : a.length = b.length) :
    diffAcc a b = 0#64 ↔ a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simp [diffAcc]
    | cons _ _ => simp at h
  | cons x xs ih =>
    cases b with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [diffAcc, List.cons.injEq]
      have h_or :
          ((x.toBitVec.setWidth 64 ^^^ y.toBitVec.setWidth 64) ||| diffAcc xs ys) = 0#64 ↔
            (x.toBitVec.setWidth 64 ^^^ y.toBitVec.setWidth 64) = 0#64 ∧ diffAcc xs ys = 0#64 := by
        grind
      have h_xy : (x.toBitVec.setWidth 64 ^^^ y.toBitVec.setWidth 64) = 0#64 ↔ x = y := by
        cases x; cases y; simp; grind
      rw [h_or, h_xy, ih ys h]

theorem diffAcc_one (a b : List UInt8) (ha : a.length = 1) (hb : b.length = 1) (acc : BitVec 64) :
    acc ||| ((BitVec.ofInt 8 (Int.ofBytes a)).setWidth 64 ^^^
             (BitVec.ofInt 8 (Int.ofBytes b)).setWidth 64) =
      acc ||| diffAcc a b := by
  rcases List.length_eq_one_iff.mp ha with ⟨x, rfl⟩
  rcases List.length_eq_one_iff.mp hb with ⟨y, rfl⟩
  rw [BitVec.ofInt_ofBytes_singleton, BitVec.ofInt_ofBytes_singleton]
  simp only [diffAcc]
  grind

theorem diffAcc_step (a b : List UInt8) (ha : 0 < a.length) (hb : 0 < b.length) (acc : BitVec 64) :
    (acc ||| ((BitVec.ofInt 8 (Int.ofBytes (a.take 1))).setWidth 64 ^^^
              (BitVec.ofInt 8 (Int.ofBytes (b.take 1))).setWidth 64)) |||
      diffAcc (a.drop 1) (b.drop 1) =
    acc ||| diffAcc a b := by
  cases a with
  | nil => simp at ha
  | cons x xs =>
    cases b with
    | nil => simp at hb
    | cons y ys =>
      simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero, diffAcc]
      rw [BitVec.ofInt_ofBytes_singleton, BitVec.ofInt_ofBytes_singleton]
      grind

theorem diffAcc_one_32 (a b : List UInt8) (ha : a.length = 1) (hb : b.length = 1) (acc : BitVec 64) :
    acc |||
      (((BitVec.ofInt 8 (Int.ofBytes a)).setWidth 32 ^^^
        (BitVec.ofInt 8 (Int.ofBytes b)).setWidth 32).setWidth 64) =
      acc ||| diffAcc a b := by
  rcases List.length_eq_one_iff.mp ha with ⟨x, rfl⟩
  rcases List.length_eq_one_iff.mp hb with ⟨y, rfl⟩
  rw [BitVec.ofInt_ofBytes_singleton, BitVec.ofInt_ofBytes_singleton]
  simp only [diffAcc]
  grind

theorem diffAcc_step_32 (a b : List UInt8) (ha : 0 < a.length) (hb : 0 < b.length) (acc : BitVec 64) :
    (acc |||
      (((BitVec.ofInt 8 (Int.ofBytes (a.take 1))).setWidth 32 ^^^
        (BitVec.ofInt 8 (Int.ofBytes (b.take 1))).setWidth 32).setWidth 64)) |||
      diffAcc (a.drop 1) (b.drop 1) =
      acc ||| diffAcc a b := by
  cases a with
  | nil => simp at ha
  | cons x xs =>
    cases b with
    | nil => simp at hb
    | cons y ys =>
      simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero, diffAcc]
      rw [BitVec.ofInt_ofBytes_singleton, BitVec.ofInt_ofBytes_singleton]
      grind

end
