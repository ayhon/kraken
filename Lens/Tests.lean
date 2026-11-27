module

import Lens
import Std.Tactic.BVDecide

/-!
# Tests and Reference Examples for `Lens`

Demonstrates how `Optic` (`Getter`, `Iso`, `Lens`, `ReflTransGen`, `Modifies`, `FactorsLawful`,
`EqOnAll`, `LensFamily`, `make_lenses`, `lens_disjoint`) covers the frame and view use cases from
`Kraken.Frame` / `Kraken.AArch64.Examples.TacticTests` in a decoupled, compositional way —
including nested heterogeneous state, derived views, sub-register slices, symbolic aliasing,
cross-universe fields, and dot-path syntax.
-/

open Optic
open scoped Optic.Notation
open scoped Optic.ProdNotation

namespace Lens.Tests

/-! ### Standalone Reference State Hierarchy (Decoupled from Kraken) -/

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

/-! ### 1. Basic Lens Operations, Composition, `Iso`, and `modifyF` -/

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

-- LawfulLens instances are synthesized automatically through composition and Iso!
example : LawfulLens stX0 := inferInstance
example : LawfulLens (stX0 ∘ₗ Iso.uint64BitVec.toLens) := inferInstance

example (st : MiniState MiniMachineData) :
    (st & stX0 .~ 42 & stZ %~ not) ^. stX0 = 42 := by
  rfl

example (st : MiniState MiniMachineData) :
    (st & stX0 .~ 42 & stZ %~ not) ^. stZ = !(st ^. stZ) := by
  rfl

-- Van Laarhoven functorial modification (`modifyF`) with `Option`:
example (st : MiniState MiniMachineData) :
    stX0.modifyF (fun v => if v == 0 then none else some (v + 1)) (st & stX0 .~ 5) =
      some (st & stX0 .~ 6) := by
  simp [Lens.modifyF]

/-! ### 2. Disjointness, Product Lenses, and Derived Views (`Getter`) -/

theorem disj_x0_x1 : Disjoint MiniRegs.Lenses.x0 MiniRegs.Lenses.x1 := by lens_disjoint
theorem disj_x3_x4 : Disjoint MiniRegs.Lenses.x3 MiniRegs.Lenses.x4 := by lens_disjoint
theorem disj_regs_flags : Disjoint MiniMachineData.Lenses.regs MiniMachineData.Lenses.flags := by
  lens_disjoint
theorem disj_regs_dmem : Disjoint MiniMachineData.Lenses.regs MiniMachineData.Lenses.dmem := by
  lens_disjoint
theorem disj_data_pc :
    Disjoint (MiniState.Lenses.data (MD := MiniMachineData)) (MiniState.Lenses.pc (MD := MiniMachineData)) := by
  lens_disjoint

-- Compositional disjointness without unfolding:
example : Disjoint stX0 stX1 :=
  Disjoint.comp_same stRegs disj_x0_x1

example : Disjoint stX0 stZ :=
  Disjoint.comp_same MiniState.Lenses.data
    (Disjoint.comp MiniRegs.Lenses.x0 MiniFlags.Lenses.z disj_regs_flags)

example : Disjoint stX0 MiniState.Lenses.pc :=
  Disjoint.comp_left _ (Disjoint.comp_left _ disj_data_pc)

-- Product of disjoint lenses is a lawful multi-register lens (e.g. a 128-bit pair):
abbrev pairX34 : Lens MiniRegs (UInt64 × UInt64) :=
  MiniRegs.Lenses.x3 ×ₗ MiniRegs.Lenses.x4

instance : LawfulLens pairX34 :=
  Lens.lawful_prod MiniRegs.Lenses.x3 MiniRegs.Lenses.x4 disj_x3_x4

-- Derived read-only views (analogous to `Reg64s.viewA`, `Reg64s.viewB`, `Reg64s.beeuX`):
abbrev MiniRegs.viewA (r : MiniRegs) : Nat := r.x0.toNat + r.x1.toNat
abbrev MiniRegs.viewB (r : MiniRegs) : Nat := r.x3.toNat + r.x4.toNat

-- Semantic independence of a derived view from an unrelated register lens is proved by `lens_disjoint`:
theorem indep_x3_viewA : Independent MiniRegs.Lenses.x3 (Getter.of MiniRegs.viewA) := by
  lens_disjoint

theorem indep_x4_viewA : Independent MiniRegs.Lenses.x4 (Getter.of MiniRegs.viewA) := by
  lens_disjoint

/-! ### 3. Product-Lens Closure Frames (`ReflTransGen (Modifies …)` and `FactorsLawful`) -/

-- `FactorsLawful` synthesizes automatically for arbitrary nested products and compositions
-- without any `Disjoint` hypotheses:
example : FactorsLawful (stPc ×ₗ stX0 ×ₗ stZ) := inferInstance
example (i j : BitVec 64) : FactorsLawful (stDmem ∘ₗ (Lens.atKey i ×ₗ Lens.atKey j)) := inferInstance

-- Concrete multi-field heterogeneous update: 1-line proof!
example (st : MiniState MiniMachineData) :
    let st' := st & stPc .~ 16 & stX0 .~ 7 & stZ .~ true
    st' ≡ₚ st except [stPc, stX0, stZ] :=
  ReflTransGen.single ⟨(16, (7, true)), rfl⟩

-- Unconditional symmetry, transitivity, and reordering without `Disjoint`:
example (r₀ r₁ r₂ : MiniRegs)
    (h₁ : r₁ ≡ₚ r₀ except [MiniRegs.Lenses.x3, MiniRegs.Lenses.x4])
    (h₂ : r₂ ≡ₚ r₁ except [MiniRegs.Lenses.x4, MiniRegs.Lenses.x3]) :
    r₀ ≡ₚ r₂ except [MiniRegs.Lenses.x3, MiniRegs.Lenses.x4] := by
  have h₂' : r₂ ≡ₚ r₁ except [MiniRegs.Lenses.x3, MiniRegs.Lenses.x4] :=
    Modifies.rt_prod_comm_iff.mp h₂
  exact Modifies.rt_symm (h₂'.trans h₁)

-- Composing frames with different write sets via `rt_prod_comp`:
example (r₀ r₁ r₂ : MiniRegs)
    (h₁ : r₁ ≡ₚ r₀ except [MiniRegs.Lenses.x3, MiniRegs.Lenses.x4])
    (h₂ : r₂ ≡ₚ r₁ except [MiniRegs.Lenses.x2]) :
    r₂ ≡ₚ r₀ except [MiniRegs.Lenses.x2, MiniRegs.Lenses.x3, MiniRegs.Lenses.x4] := by
  have h := Modifies.rt_prod_comp h₁ h₂
  exact Modifies.rt_prod_comm_iff.mp h

-- Narrowing an `except` frame into an `on` frame over registers and derived views:
example (r' r : MiniRegs)
    (h : r' ≡ₚ r except [MiniRegs.Lenses.x3, MiniRegs.Lenses.x4]) :
    r' ≡ₚ r on [MiniRegs.Lenses.sp, MiniRegs.Lenses.x0, MiniRegs.viewA] := by
  refine Modifies.rt_preserves_all ?_ h
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> exact fun _ _ => rfl

-- Lifting a register-file closure frame to the whole `MiniState`:
example (st : MiniState MiniMachineData) (r' : MiniRegs)
    (h : r' ≡ₚ (st ^. stRegs) except [MiniRegs.Lenses.x3, MiniRegs.Lenses.x4]) :
    (st & stRegs .~ r') ≡ₚ st except [stRegs ∘ₗ MiniRegs.Lenses.x3, stRegs ∘ₗ MiniRegs.Lenses.x4] :=
  Modifies.rt_lift_prod stRegs h

-- Empty write set (`except []`) collapses to `Eq`:
example (st' st : MiniState MiniMachineData) :
    (st' ≡ₚ st except []) ↔ st' = st :=
  Modifies.rt_unit_iff

-- Cross-universe frames work out of the box because `Prod` is universe-polymorphic:
structure PolyState where
  val0 : UInt64  -- Type 0
  ty1 : Type 0   -- Type 1

make_lenses PolyState

example (s' s : PolyState)
    (h : s' ≡ₚ s except [PolyState.Lenses.val0]) :
    s'.ty1 = s.ty1 :=
  Modifies.rt_preserves (g := PolyState.Lenses.ty1.toGetter) (fun _ _ => rfl) h

/-! ### 4. Symbolic Aliasing Without `Disjoint` (`Lens.atKey` for Memory) -/

-- Interleaved writes `i → j → i` compose unconditionally in `ReflTransGen (Modifies (atKey i ×ₗ atKey j))`
-- WITHOUT knowing whether `i = j` or `i ≠ j`, and still preserve any third address `k` with `k ≠ i, k ≠ j`:
example (m₀ m₁ m₂ m₃ : BitVec 64 → UInt8) (i j k : BitVec 64)
    (hki : k ≠ i) (hkj : k ≠ j)
    (h₁ : Modifies (Lens.atKey i) m₁ m₀)
    (h₂ : Modifies (Lens.atKey j) m₂ m₁)
    (h₃ : Modifies (Lens.atKey i) m₃ m₂) :
    (m₃ ≡ₚ m₀ except [Lens.atKey i, Lens.atKey j]) ∧ m₃ k = m₀ k := by
  have h123 : m₃ ≡ₚ m₀ except [Lens.atKey i, Lens.atKey j] :=
    (Modifies.rt_prod_left (Lens.atKey j) (Modifies.rt_single h₃)).trans
      ((Modifies.rt_prod_right (Lens.atKey i) (Modifies.rt_single h₂)).trans
        (Modifies.rt_prod_left (Lens.atKey j) (Modifies.rt_single h₁)))
  refine ⟨h123, ?_⟩
  have hind : Independent (Lens.atKey (v := UInt8) i ×ₗ Lens.atKey (v := UInt8) j)
      (Lens.atKey (v := UInt8) k).toGetter :=
    Independent.prod_lens
      (Disjoint.atKey_of_ne hki.symm).independent_left
      (Disjoint.atKey_of_ne hkj.symm).independent_left
  exact Modifies.rt_preserves hind h123

/-! ### 5. Sub-Register Bit-Slice Lenses and Overlapping Coarsening -/

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

theorem disj_low8_high8 : Disjoint low8 high8 := by
  intro x v₁ v₂; simp only [low8, high8]; bv_decide

abbrev stX0Low8 : Lens (MiniState MiniMachineData) (BitVec 8) :=
  (stX0 ∘ₗ Iso.uint64BitVec.toLens) ∘ₗ low8

abbrev stX0High8 : Lens (MiniState MiniMachineData) (BitVec 8) :=
  (stX0 ∘ₗ Iso.uint64BitVec.toLens) ∘ₗ high8

-- Writing `al` preserves `ah`:
example (st : MiniState MiniMachineData) (v : BitVec 8) :
    ((st & stX0Low8 .~ v) ^. stX0High8) = (st ^. stX0High8) := by
  have hdisj : Disjoint stX0Low8 stX0High8 :=
    Disjoint.comp_same (stX0 ∘ₗ Iso.uint64BitVec.toLens) disj_low8_high8
  exact Modifies.preserves_disjoint hdisj (Modifies.set _ _ _)

-- Overlapping writes `[stX0Low8, stX0]` absorb cleanly into `[stX0]` without `Disjoint`:
example (st' st : MiniState MiniMachineData)
    (h : st' ≡ₚ st except [stX0Low8, stX0]) :
    st' ≡ₚ st except [stX0] := by
  have h1 : st' ≡ₚ st except [stX0 ∘ₗ Iso.uint64BitVec.toLens, stX0] := by
    refine h.mono_rt (fun _ _ hm => ?_)
    rcases Modifies.prod_iff_exists.mp hm with ⟨_, hlow, hx0⟩
    exact (Modifies.rt_single (Modifies.prod_right _ hx0)).trans
      (Modifies.rt_single (Modifies.prod_left _ (Modifies.coarsen hlow)))
  exact Modifies.rt_prod_comp_left_iff.mp h1

/-! ### 6. Structure-Update & Declarative `is { … with … except … }` Dot-Path Syntax -/

example (st : MiniState MiniMachineData) :
    (st ^. data.regs.x0) = (st ^. stX0) := rfl

example (st : MiniState MiniMachineData) :
    {ₗ st with pc := 16, data.regs.x0 over (· + 1), data.flags.z over not } =
      (st & stPc .~ 16 & stX0 %~ (· + 1) & stZ %~ not) := rfl

example (s₀ st : MiniState MiniMachineData)
    (h : st is { s₀ with pc := 16, data.regs.x0 over (· + 1) except data.flags }) :
    st ^. pc = 16 ∧ st ^. data.regs.x0 = (s₀ ^. data.regs.x0) + 1 ∧
      st ^. data.dmem = s₀ ^. data.dmem :=
  ⟨Modifies.rt_preserves (g := stPc.toGetter) (fun _ _ => rfl) h,
   Modifies.rt_preserves (g := stX0.toGetter) (fun _ _ => rfl) h,
   Modifies.rt_preserves (g := stDmem.toGetter) (s₀ := {ₗ s₀ with pc := 16, data.regs.x0 over (· + 1) })
     (fun _ _ => rfl) h⟩

/-! ### 7. `LensFamily` and the Bridge Theorem (Recovering `RegFile.EqExcept`) -/

inductive MiniRegName where
  | x0 | x1 | x2 | x3 | x4 | sp
  deriving DecidableEq

def miniRegFamily : LensFamily MiniRegs MiniRegName (fun _ => UInt64) where
  lens
    | .x0 => MiniRegs.Lenses.x0
    | .x1 => MiniRegs.Lenses.x1
    | .x2 => MiniRegs.Lenses.x2
    | .x3 => MiniRegs.Lenses.x3
    | .x4 => MiniRegs.Lenses.x4
    | .sp => MiniRegs.Lenses.sp

instance : LawfulLensFamily miniRegFamily where
  lawful i := by cases i <;> dsimp only [miniRegFamily] <;> infer_instance
  disjoint i j hne := by
    cases i <;> cases j
    all_goals first | exact absurd rfl hne | lens_disjoint
  ext r₁ r₂ h := by
    cases r₁; cases r₂
    have h0 := h .x0; have h1 := h .x1; have h2 := h .x2
    have h3 := h .x3; have h4 := h .x4; have h5 := h .sp
    dsimp [miniRegFamily] at h0 h1 h2 h3 h4 h5
    subst h0 h1 h2 h3 h4 h5
    rfl

-- Exact equivalence between `ReflTransGen (Modifies (F.prodLens W))` and pointwise `EqExcept`:
example (r' r : MiniRegs) :
    (r' ≡ₚ r except [MiniRegs.Lenses.x3, MiniRegs.Lenses.x4]) ↔
      ∀ n : MiniRegName, n ∉ [.x3, .x4] →
        (miniRegFamily.lens n).get r' = (miniRegFamily.lens n).get r :=
  LawfulLensFamily.rt_modifies_prodLens_iff miniRegFamily [.x3, .x4] r' r

end Lens.Tests
