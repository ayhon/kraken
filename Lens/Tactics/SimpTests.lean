module

import Lens
import Lens.Tactics.Simp
import Std.Tactic.BVDecide

/-!
# Tests for `lens_simp` and `lens_dsimp` (`Lens.Tactics.Simp`)

Verifies:
1. Abstract polymorphic lenses with `[LawfulLens]` and `Disjoint` hypotheses (disjoint reads,
   nested reads, dead-overwrite collapse across disjoint writes, `Lens.over` fusion/commutation,
   `set_get`, `Getter` combinators, `Iso`).
2. Concrete nested struct lenses, `{ₗ st with … }` updates, `Lens.atKey` (local inequality,
   `decide`, `omega`), bit-slices (`low8`/`high8` via `@[lens_disjoint]`), raw structure
   projections, derived views (`stateViewA`, `stateViewMem`, `Getter.of`), and opaque function
   preservation.
3. Location modifiers (`at h`, `at *`), extra lemmas (`lens_simp [h]`), `lens_simp only`, and
   extensible `@[lens_simp]`.
4. `lens_dsimp` pure definitional reduction (`lens_dsimp; rfl`, `lens_dsimp at h`, `lens_dsimp at *`).
-/

open Optic
open scoped Optic.Notation

namespace Lens.Tactics.SimpTests

/-! ### 1. Abstract Polymorphic Lenses -/

section AbstractLenses

variable {S A B C : Type}

example (l : Lens S A) (k : Lens S B) [LawfulLens k]
    (h : Disjoint l k) (s : S) (v : A) :
    k.get (l.set s v) = k.get s := by
  lens_simp

example (l : Lens S A) (k : Lens S B) [LawfulLens l] [LawfulLens k]
    (h : Disjoint l k) (s : S) (v : A) (w : B) :
    l.get (k.set (l.set s v) w) = v := by
  lens_simp

-- Dead overwrite collapse across a disjoint write:
example (l : Lens S A) (k : Lens S B) [LawfulLens l]
    (h : Disjoint l k) (s : S) (v₁ v₂ : A) (w : B) :
    l.set (k.set (l.set s v₁) w) v₂ = k.set (l.set s v₂) w := by
  lens_simp

-- Dead overwrite collapse across MULTIPLE disjoint writes (mix of `set` and `over`):
example (l : Lens S A) (k₁ : Lens S B) (k₂ : Lens S C)
    [LawfulLens l] [LawfulLens k₂]
    (h₁ : Disjoint l k₁) (h₂ : Disjoint l k₂)
    (s : S) (v₁ v₂ : A) (w : B) (g : C → C) :
    l.set (k₁.set (k₂.over g (l.set s v₁)) w) v₂ =
      k₁.set (k₂.over g (l.set s v₂)) w := by
  lens_simp

-- Dead `over` overwritten by `set` across a disjoint write:
example (l : Lens S A) (k : Lens S B) [LawfulLens l]
    (h : Disjoint l k) (s : S) (f : A → A) (w : B) (v : A) :
    l.set (k.set (l.over f s) w) v = k.set (l.set s v) w := by
  lens_simp

-- `over` through disjoint `over`:
example (l : Lens S A) (k : Lens S B) [LawfulLens l] [LawfulLens k]
    (h : Disjoint l k) (s : S) (f : A → A) (g : B → B) :
    l.get (k.over g (l.over f s)) = f (l.get s) := by
  lens_simp

-- `over` merged into `set` across a disjoint write:
example (l : Lens S A) (k : Lens S B) [LawfulLens l]
    (h : Disjoint l k) (s : S) (f : A → A) (v : A) (w : B) :
    l.over f (k.set (l.set s v) w) = k.set (l.set s (f v)) w := by
  lens_simp

-- `set_get` and identity `over` (both `id` and lambda `fun x => x`):
example (l : Lens S A) [LawfulLens l] (s : S) :
    l.set s (l.get s) = s := by
  lens_simp

example (l : Lens S A) [LawfulLens l] (s : S) :
    l.over (fun x => x) s = s := by
  lens_simp

-- `Getter` independence and combinators:
example (l : Lens S A) (g : Getter S B) (h : Independent l g) (s : S) (v : A) :
    g.get (l.set s v) = g.get s := by
  lens_simp

example (l : Lens S A) (g : Getter S B) (h : Independent l g) (f : B → C) (s : S) (v : A) :
    (g.map f).get (l.set s v) = f (g.get s) := by
  lens_simp

example (l : Lens S A) (g : Getter S B) (h : Independent l g) (fn : A → A) (s : S) :
    g.get (l.over fn s) = g.get s := by
  lens_simp

-- Primitive lenses (`id`, `unit`, `fst`, `snd`, `prod`) and `Iso`:
example (p : A × B) (x : A) (y : B) :
    ((p & Lens.fst .~ x & Lens.snd .~ y) ^. Lens.fst (a := A) (b := B)) = x := by
  lens_simp

example (l₁ : Lens S A) (l₂ : Lens S B) [LawfulLens l₁] [LawfulLens l₂]
    (h : Disjoint l₁ l₂) (s : S) (a : A) (b : B) :
    ((s & (l₁ ×ₗ l₂) .~ (a, b)) ^. l₁) = a := by
  lens_simp

example (s : S) (x : PUnit) :
    (s & Lens.unit .~ x) = s := by
  lens_simp

example (i : Iso S A) [LawfulIso i] (s : S) :
    i.inv (i.to s) = s := by
  lens_simp

end AbstractLenses

/-! ### 2. Concrete Nested Struct Lenses, Bit-Slices, `atKey`, Derived Views -/

structure MiniRegs where
  x0 : UInt64 := 0
  x1 : UInt64 := 0
  x2 : UInt64 := 0
  x3 : UInt64 := 0
  x4 : UInt64 := 0
  sp : UInt64 := 0
  deriving Repr, DecidableEq

structure MiniFlags where
  n : Bool := false
  z : Bool := false
  c : Bool := false
  v : Bool := false
  deriving Repr, DecidableEq

structure MiniMachineData where
  regs : MiniRegs
  flags : MiniFlags
  dmem : BitVec 64 → UInt8

structure MiniState (MD : Type) where
  data : MD
  pc : Int64

make_lenses MiniRegs
make_lenses MiniFlags
make_lenses MiniMachineData
make_lenses MiniState

abbrev stRegs : Lens (MiniState MiniMachineData) MiniRegs :=
  MiniState.Lenses.data ∘ₗ MiniMachineData.Lenses.regs

abbrev stFlags : Lens (MiniState MiniMachineData) MiniFlags :=
  MiniState.Lenses.data ∘ₗ MiniMachineData.Lenses.flags

abbrev stDmem : Lens (MiniState MiniMachineData) (BitVec 64 → UInt8) :=
  MiniState.Lenses.data ∘ₗ MiniMachineData.Lenses.dmem

abbrev stX0 : Lens (MiniState MiniMachineData) UInt64 :=
  stRegs ∘ₗ MiniRegs.Lenses.x0

abbrev stX1 : Lens (MiniState MiniMachineData) UInt64 :=
  stRegs ∘ₗ MiniRegs.Lenses.x1

abbrev stSp : Lens (MiniState MiniMachineData) UInt64 :=
  stRegs ∘ₗ MiniRegs.Lenses.sp

abbrev stZ : Lens (MiniState MiniMachineData) Bool :=
  stFlags ∘ₗ MiniFlags.Lenses.z

abbrev stPc : Lens (MiniState MiniMachineData) Int64 :=
  MiniState.Lenses.pc

def low8 : Lens (BitVec 64) (BitVec 8) where
  get x := x.extractLsb' 0 8
  set x v := (x &&& ~~~0xFF#64) ||| v.zeroExtend 64

def high8 : Lens (BitVec 64) (BitVec 8) where
  get x := x.extractLsb' 8 8
  set x v := (x &&& ~~~0xFF00#64) ||| (v.zeroExtend 64 <<< 8)

instance : LawfulLens low8 where
  get_set x v := by simp only [low8]; bv_decide
  set_get x := by simp only [low8]; bv_decide
  set_set x v₁ v₂ := by simp only [low8]; bv_decide

instance : LawfulLens high8 where
  get_set x v := by simp only [high8]; bv_decide
  set_get x := by simp only [high8]; bv_decide
  set_set x v₁ v₂ := by simp only [high8]; bv_decide

@[lens_disjoint] theorem disj_low8_high8 : Disjoint low8 high8 := by
  intro x v₁ v₂; simp only [low8, high8]; bv_decide

abbrev stX0Low8 : Lens (MiniState MiniMachineData) (BitVec 8) :=
  (stX0 ∘ₗ Iso.uint64BitVec.toLens) ∘ₗ low8

abbrev stX0High8 : Lens (MiniState MiniMachineData) (BitVec 8) :=
  (stX0 ∘ₗ Iso.uint64BitVec.toLens) ∘ₗ high8

def stateViewA (st : MiniState MiniMachineData) : Nat :=
  st.data.regs.x0.toNat + st.data.regs.x1.toNat

def stateViewMem (addr : BitVec 64) (st : MiniState MiniMachineData) : Nat :=
  st.data.regs.sp.toNat + (st.data.dmem addr).toNat

-- Bit-slice disjoint read via `@[lens_disjoint]`:
example (st : MiniState MiniMachineData) (v : BitVec 8) :
    ((st & stX0Low8 .~ v) ^. stX0High8) = (st ^. stX0High8) := by
  lens_simp

-- Bit-slice dead overwrite collapse across another disjoint slice:
example (st : MiniState MiniMachineData) (v₁ v₂ w : BitVec 8) :
    (st & stX0Low8 .~ v₁ & stX0High8 .~ w & stX0Low8 .~ v₂) =
      (st & stX0Low8 .~ v₂ & stX0High8 .~ w) := by
  lens_simp

-- `atKey` disjoint read via local inequality:
example (st : MiniState MiniMachineData) (a₁ a₂ : BitVec 64) (b : UInt8) (hne : a₁ ≠ a₂) :
    ((st & (stDmem ∘ₗ Lens.atKey a₁) .~ b) ^. (stDmem ∘ₗ Lens.atKey a₂)) =
      (st ^. (stDmem ∘ₗ Lens.atKey a₂)) := by
  lens_simp

-- `atKey` disjoint read with reversed inequality and raw map-lookup RHS:
example (st : MiniState MiniMachineData) (a₁ a₂ : BitVec 64) (b : UInt8) (hne : a₂ ≠ a₁) :
    ((st & (stDmem ∘ₗ Lens.atKey a₁) .~ b).data.dmem a₂) = st.data.dmem a₂ := by
  lens_simp

-- `atKey` via `decide` (concrete addresses) and `omega` (symbolic Nat):
example (st : MiniState MiniMachineData) (b : UInt8) :
    ((st & (stDmem ∘ₗ Lens.atKey (0 : BitVec 64)) .~ b) ^. (stDmem ∘ₗ Lens.atKey (8 : BitVec 64))) =
      (st ^. (stDmem ∘ₗ Lens.atKey (8 : BitVec 64))) := by
  lens_simp

example (m : Nat → UInt8) (i : Nat) (b : UInt8) :
    ((m & Lens.atKey i .~ b) ^. Lens.atKey (v := UInt8) (i + 1)) = m (i + 1) := by
  lens_simp

-- Derived view preservation (plain user `def` and parameterized view):
example (st : MiniState MiniMachineData) :
    stateViewA (st & stPc .~ 16 & stZ .~ true) = stateViewA st := by
  lens_simp

example (st : MiniState MiniMachineData) (a₁ a₂ : BitVec 64) (b : UInt8) (hne : a₁ ≠ a₂) :
    stateViewMem a₂ (st & (stDmem ∘ₗ Lens.atKey a₁) .~ b & stX0 .~ 99) = stateViewMem a₂ st := by
  lens_simp

-- `{ₗ st with … }` dot-path updates and raw structure projections:
example (st : MiniState MiniMachineData) :
    ({ₗ st with pc := 16, data.regs.x0 := 42, data.flags.z over not } ^. data.regs.x0) = 42 := by
  lens_simp

example (st : MiniState MiniMachineData) :
    ({ₗ st with pc := 16, data.flags.z over not }).data.regs.x0 = st.data.regs.x0 := by
  lens_simp

example (st : MiniState MiniMachineData) (r : MiniRegs) :
    ((st & stRegs .~ r) ^. stX0) = r.x0 := by
  lens_simp

example (st : MiniState MiniMachineData) :
    (st & stX0 .~ st.data.regs.x0) = st := by
  lens_simp

-- Opaque / non-reducible helper function is NOT unfolded by `lens_simp`:
def opaqueStep (n : UInt64) : UInt64 := n + 1

example (st : MiniState MiniMachineData) (h : opaqueStep (st ^. stX0) = 10) :
    ((st & stX0 %~ opaqueStep & stPc .~ 16) ^. stX0) = 10 := by
  lens_simp
  exact h

/-! ### 3. Location Modifiers (`at h`, `at *`), Extra Lemmas, `only`, and `@[lens_simp]` -/

example (st : MiniState MiniMachineData) (v : BitVec 8)
    (h : ((st & stX0Low8 .~ v) ^. stX0High8) = 7#8) :
    (st ^. stX0High8) = 7#8 := by
  lens_simp at h
  exact h

example (st : MiniState MiniMachineData) (v : UInt64)
    (h : ({ₗ st with pc := 16, data.regs.x0 := v } ^. data.regs.x0) = 99) :
    ((st & stPc .~ 8 & stX0 .~ v & stZ .~ true) ^. stX0) = 99 := by
  lens_simp at *
  exact h

example (st : MiniState MiniMachineData) (h : st ^. stX0 = 5) :
    ((st & stPc .~ 16) ^. stX0) = 5 := by
  lens_simp [h]

example (st : MiniState MiniMachineData) (h : st ^. stX0 = 5) :
    ((st & stPc .~ 16) ^. stX0) = 5 := by
  lens_simp [*]

-- Dead overwrites and restored `set_get` across disjoint writes collapse without exploding structs:
example (st : MiniState MiniMachineData) (P : MiniState MiniMachineData → Prop)
    (h : P (stX0.set st 42)) :
    P (st & stX0 .~ 1 & stPc .~ 16 & stX0 .~ 42 & stPc .~ st.pc) := by
  lens_simp
  exact h

-- `@[lens_simp]` attribute also works with standard `simp only [lens_simp]`:
example {S A : Type} (l : Lens S A) [LawfulLens l] (s : S) (v₁ v₂ : A) :
    l.get (l.set (l.set s v₁) v₂) = v₂ := by
  simp only [lens_simp]

example (st : MiniState MiniMachineData) (v : BitVec 8) :
    ((st & stX0Low8 .~ v) ^. stX0High8) = (st ^. stX0High8) := by
  lens_simp only [Optic.HasGet.getOf_lens]

-- Custom user `@[lens_simp]` lemma:
def customTag (n : Nat) : Nat := n

@[lens_simp] theorem customTag_eq (n : Nat) : customTag n = n := rfl

example (st : MiniState MiniMachineData) :
    customTag (stateViewA (st & stPc .~ 16)) = stateViewA st := by
  lens_simp

/-! ### 4. Targeted Definitional Reduction (`lens_dsimp`) -/

example (st : MiniState MiniMachineData) :
    ({ₗ st with pc := 16, data.regs.x0 := 42, data.flags.z over not } ^. data.regs.x0) = 42 := by
  lens_dsimp; rfl

example (st : MiniState MiniMachineData) :
    ({ₗ st with pc := 16, data.regs.x0 := 42, data.flags.z over not } ^. data.flags.z) = !st.data.flags.z := by
  lens_dsimp; rfl

example (st : MiniState MiniMachineData)
    (h : ({ₗ st with pc := 16, data.regs.x0 := 42, data.flags.z over not } ^. data.regs.x0) = 42 → False) :
    False := by
  lens_dsimp at h
  exact h rfl

example (st : MiniState MiniMachineData) (y : UInt64)
    (h : ({ₗ st with pc := 16, data.regs.x0 := 42, data.flags.z over not } ^. data.regs.x0) = y) :
    y = 42 := by
  lens_dsimp at h
  exact h.symm

example (st : MiniState MiniMachineData) (y : UInt64)
    (h : (st & stPc .~ 16 & stX0 .~ 42) ^. stX0 = y) :
    ((st & stZ .~ true & stX0 .~ y) ^. stX0) = 42 := by
  lens_dsimp at *
  exact h.symm

-- `lens_dsimp` does NOT unfold opaque user functions:
example (st : MiniState MiniMachineData) (h : opaqueStep 42 = 43) :
    opaqueStep ({ₗ st with pc := 16, data.regs.x0 := 42 } ^. data.regs.x0) = 43 := by
  lens_dsimp
  exact h

end Lens.Tactics.SimpTests
