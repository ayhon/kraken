module

import Lens
import Lens.Tactics.Frame
import Std.Tactic.BVDecide

/-!
# Comprehensive Tests for `lens_frame` (`Lens/Tactics/Frame.lean`)

Covers:
1. Engine A: concrete raw structure updates (`{ s₀ with … }`, `S.mk …`) with extra untouched slots.
2. Engine A: concrete lens updates (`{ₗ s₀ with … }`, `&`, `.~`, `%~`, `Lens.set`, `Lens.over`).
3. Engine B: transitivity, permutation, weakening, deduplication, symmetry — including symbolic
   `atKey i ×ₗ atKey j` WITHOUT `i ≠ j` (zero `Disjoint` obligations).
4. Hierarchical coarsening (`stX0Low8` covered by `stX0`, `stRegs`, `MiniState.Lenses.data`).
5. Substate lifting (`r' ≡ₚ st.data.regs except [x3, x4]` into both raw struct updates and lens sets).
6. Declarative `st is { s₀ with … except … }` goals (concrete, reordered, and context-backed).
7. Engine C: `EqOn` and `≡ₚ … on […]` narrowing (fields, `atKey`, `MiniRegs.viewA`, `stateViewA`,
   `stateViewMem`, concrete updates, partial open subgoals).
8. Empty write-set `except []`, single-pass `Modifies`, and cross-universe `PolyState`.
9. Missing-write UX diagnostics (`lens_frame: add to writes: [...]`) + focused equality subgoals.
-/

open Optic
open scoped Optic.Notation
open scoped Optic.ProdNotation

namespace Lens.Tactics.FrameTests

/-! ### Standalone Test Hierarchy -/

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

abbrev stData : Lens (MiniState MiniMachineData) MiniMachineData :=
  MiniState.Lenses.data

abbrev stRegs : Lens (MiniState MiniMachineData) MiniRegs :=
  MiniState.Lenses.data ∘ₗ MiniMachineData.Lenses.regs

abbrev stFlags : Lens (MiniState MiniMachineData) MiniFlags :=
  MiniState.Lenses.data ∘ₗ MiniMachineData.Lenses.flags

abbrev stDmem : Lens (MiniState MiniMachineData) (BitVec 64 → UInt8) :=
  MiniState.Lenses.data ∘ₗ MiniMachineData.Lenses.dmem

abbrev stX0 : Lens (MiniState MiniMachineData) UInt64 := stRegs ∘ₗ MiniRegs.Lenses.x0
abbrev stX1 : Lens (MiniState MiniMachineData) UInt64 := stRegs ∘ₗ MiniRegs.Lenses.x1
abbrev stX2 : Lens (MiniState MiniMachineData) UInt64 := stRegs ∘ₗ MiniRegs.Lenses.x2
abbrev stX3 : Lens (MiniState MiniMachineData) UInt64 := stRegs ∘ₗ MiniRegs.Lenses.x3
abbrev stX4 : Lens (MiniState MiniMachineData) UInt64 := stRegs ∘ₗ MiniRegs.Lenses.x4
abbrev stSp : Lens (MiniState MiniMachineData) UInt64 := stRegs ∘ₗ MiniRegs.Lenses.sp
abbrev stZ  : Lens (MiniState MiniMachineData) Bool   := stFlags ∘ₗ MiniFlags.Lenses.z
abbrev stN  : Lens (MiniState MiniMachineData) Bool   := stFlags ∘ₗ MiniFlags.Lenses.n
abbrev stPc : Lens (MiniState MiniMachineData) Int64  := MiniState.Lenses.pc

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

abbrev MiniRegs.viewA (r : MiniRegs) : Nat := r.x0.toNat + r.x1.toNat
abbrev MiniRegs.viewB (r : MiniRegs) : Nat := r.x3.toNat + r.x4.toNat

def stateViewA (st : MiniState MiniMachineData) : Nat :=
  st.data.regs.x0.toNat + st.data.regs.x1.toNat

def stateViewMem (addr : BitVec 64) (st : MiniState MiniMachineData) : Nat :=
  st.data.regs.sp.toNat + (st.data.dmem addr).toNat

structure PolyState where
  val0 : UInt64
  ty1 : Type 0

make_lenses PolyState

/-! ### 1. Engine A: Concrete Raw Structure Updates -/

example (s₀ : MiniMachineData) :
    { s₀ with regs := { s₀.regs with x0 := 1, x2 := 2 } }
      ≡ₚ s₀ except [MiniMachineData.Lenses.regs ∘ₗ MiniRegs.Lenses.x0,
                    MiniMachineData.Lenses.regs ∘ₗ MiniRegs.Lenses.x2] := by
  lens_frame

-- Extra untouched slots in `except` (including `atKey` untouched slot forcing step-by-step chain!)
example (s₀ : MiniMachineData) :
    { s₀ with regs := { s₀.regs with x0 := 1, x2 := 2 } }
      ≡ₚ s₀ except [MiniMachineData.Lenses.flags ∘ₗ MiniFlags.Lenses.z,
                    MiniMachineData.Lenses.regs ∘ₗ MiniRegs.Lenses.x2,
                    MiniMachineData.Lenses.regs ∘ₗ MiniRegs.Lenses.x0,
                    MiniMachineData.Lenses.regs ∘ₗ MiniRegs.Lenses.sp] := by
  lens_frame

example (s₀ : MiniMachineData) (a : BitVec 64) :
    { s₀ with regs := { s₀.regs with x0 := 1, x2 := 2 } }
      ≡ₚ s₀ except [MiniMachineData.Lenses.dmem ∘ₗ Lens.atKey a,
                    MiniMachineData.Lenses.regs ∘ₗ MiniRegs.Lenses.x0,
                    MiniMachineData.Lenses.regs ∘ₗ MiniRegs.Lenses.x2] := by
  lens_frame

-- Explicit constructor `S.mk …` + nested state
example (st : MiniState MiniMachineData) :
    MiniState.mk { st.data with regs := { st.data.regs with x0 := 10 } } (st.pc + 4)
      ≡ₚ st except [stPc, stX0, stZ] := by
  lens_frame

-- Single-pass `Modifies` on concrete raw struct update
example (s₀ : MiniMachineData) :
    Modifies ((MiniMachineData.Lenses.regs ∘ₗ MiniRegs.Lenses.x0) ×ₗ
              (MiniMachineData.Lenses.regs ∘ₗ MiniRegs.Lenses.x2))
      { s₀ with regs := { s₀.regs with x0 := 1, x2 := 2 } } s₀ := by
  lens_frame

-- Raw struct update with `atKey` update inside `dmem`
example (st : MiniState MiniMachineData) (a b : BitVec 64) (v : UInt8) :
    { st with
        pc := st.pc + 4,
        data := { st.data with dmem := (Lens.atKey a).set st.data.dmem v } }
      ≡ₚ st except [stPc, stDmem ∘ₗ Lens.atKey a, stDmem ∘ₗ Lens.atKey b] := by
  lens_frame

/-! ### 2. Engine A: Concrete Lens Updates (`{ₗ … with … }`, `&`, `.~`, `%~`) -/

example (st : MiniState MiniMachineData) :
    {ₗ st with pc := 16, data.regs.x0 over (· + 1) }
      ≡ₚ st except [stPc, stX0] := by
  lens_frame

example (st : MiniState MiniMachineData) :
    {ₗ st with pc := 16, data.regs.x0 over (· + 1), data.flags.z over not }
      ≡ₚ st except [stZ, stX0, stPc, stX1] := by
  lens_frame

example (st : MiniState MiniMachineData) :
    let st' := st & stPc .~ 16 & stX0 .~ 7 & stZ %~ not
    st' ≡ₚ st except [stPc, stX0, stZ] := by
  lens_frame

example (st : MiniState MiniMachineData) (a : BitVec 64) (v : UInt8) :
    {ₗ st with pc := 16, data.regs.x0 over (· + 1) }
      ≡ₚ st except [stDmem ∘ₗ Lens.atKey a, stX0, stPc] := by
  let _ := v
  lens_frame

-- Single-pass `Modifies` on concrete lens update (different order, disjoint factors)
example (st : MiniState MiniMachineData) :
    Modifies (stX0 ×ₗ stPc) {ₗ st with pc := 16, data.regs.x0 := 7 } st := by
  lens_frame

-- Nested raw struct inside `Lens.set` covered by finer write-set
example (st : MiniState MiniMachineData) :
    stRegs.set st { st.data.regs with x0 := 42 } ≡ₚ st except [stX0] := by
  lens_frame

/-! ### 3. Engine B: Transitivity, Permutation, Weakening, Deduplication, Symmetry -/

example (r₀ r₁ r₂ : MiniRegs)
    (h₁ : r₁ ≡ₚ r₀ except [MiniRegs.Lenses.x3, MiniRegs.Lenses.x4])
    (h₂ : r₂ ≡ₚ r₁ except [MiniRegs.Lenses.x4, MiniRegs.Lenses.x3]) :
    r₀ ≡ₚ r₂ except [MiniRegs.Lenses.x3, MiniRegs.Lenses.x4] := by
  lens_frame

-- Weakening + permutation + multi-step transitivity + deduplication
example (r₀ r₁ r₂ r₃ : MiniRegs)
    (h₁ : r₁ ≡ₚ r₀ except [MiniRegs.Lenses.x3, MiniRegs.Lenses.x3])
    (h₂ : Modifies MiniRegs.Lenses.x2 r₂ r₁)
    (h₃ : r₂ ≡ₚ r₃ except [MiniRegs.Lenses.x4, MiniRegs.Lenses.x3]) :
    r₃ ≡ₚ r₀ except [MiniRegs.Lenses.x4, MiniRegs.Lenses.x2, MiniRegs.Lenses.x3, MiniRegs.Lenses.x0] := by
  lens_frame

-- Symbolic `atKey i ×ₗ atKey j` WITHOUT `i ≠ j` (zero `Disjoint` obligations!)
example (m₀ m₁ m₂ m₃ : BitVec 64 → UInt8) (i j : BitVec 64)
    (h₁ : Modifies (Lens.atKey i) m₁ m₀)
    (h₂ : Modifies (Lens.atKey j) m₂ m₁)
    (h₃ : Modifies (Lens.atKey i) m₃ m₂) :
    m₃ ≡ₚ m₀ except [Lens.atKey i, Lens.atKey j] := by
  lens_frame

-- Symbolic permutation + symmetry on `atKey i ×ₗ atKey j` WITHOUT `i ≠ j`!
example (m₀ m₁ m₂ : BitVec 64 → UInt8) (i j : BitVec 64)
    (h₁ : m₁ ≡ₚ m₀ except [Lens.atKey j, Lens.atKey i])
    (h₂ : m₁ ≡ₚ m₂ except [Lens.atKey i, Lens.atKey j]) :
    m₂ ≡ₚ m₀ except [Lens.atKey i, Lens.atKey j] := by
  lens_frame

-- Product under shared outer lens (`stDmem ∘ₗ (atKey i ×ₗ atKey j)`)
example (st₀ st₁ st₂ : MiniState MiniMachineData) (i j : BitVec 64)
    (h₁ : st₁ ≡ₚ st₀ except [stDmem ∘ₗ Lens.atKey i])
    (h₂ : st₂ ≡ₚ st₁ except [stDmem ∘ₗ Lens.atKey j]) :
    st₂ ≡ₚ st₀ except [stDmem ∘ₗ (Lens.atKey j ×ₗ Lens.atKey i)] := by
  lens_frame

-- Single-pass `Modifies` from context `ReflTransGen` via automatic `LawfulLens` (`Lens.lawful_prod` + `proveDisjoint?`)
example (r₀ r₁ r₂ : MiniRegs)
    (h₁ : r₁ ≡ₚ r₀ except [MiniRegs.Lenses.x3])
    (h₂ : r₂ ≡ₚ r₁ except [MiniRegs.Lenses.x4]) :
    Modifies (MiniRegs.Lenses.x3 ×ₗ MiniRegs.Lenses.x4) r₂ r₀ := by
  lens_frame

-- Context mixing `Eq`, `let`, concrete updates, and `ReflTransGen`
example (s₀ s₁ s₂ : MiniState MiniMachineData)
    (h₁ : s₁ = {ₗ s₀ with pc := 16 })
    (h₂ : s₂ ≡ₚ s₁ except [stX0]) :
    s₂ ≡ₚ s₀ except [stX0, stPc] := by
  lens_frame

/-! ### 4. Hierarchical Coarsening (`stX0Low8` → `stX0` / `stRegs` / `data`) -/

example (st : MiniState MiniMachineData) (v : BitVec 8) :
    (st & stX0Low8 .~ v) ≡ₚ st except [stX0] := by
  lens_frame

example (st : MiniState MiniMachineData) (v : BitVec 8) :
    (st & stX0Low8 .~ v) ≡ₚ st except [stRegs] := by
  lens_frame

example (st : MiniState MiniMachineData) (v : BitVec 8) :
    (st & stX0Low8 .~ v) ≡ₚ st except [stData] := by
  lens_frame

example (st' st : MiniState MiniMachineData)
    (h : st' ≡ₚ st except [stX0Low8, stX0]) :
    st' ≡ₚ st except [stX0] := by
  lens_frame

example (st₀ st₁ st₂ : MiniState MiniMachineData)
    (h₁ : st₁ ≡ₚ st₀ except [stX0Low8])
    (h₂ : st₂ ≡ₚ st₁ except [stZ]) :
    st₂ ≡ₚ st₀ except [stData] := by
  lens_frame

/-! ### 5. Substate Lifting -/

-- Raw nested structure update lifting substate frame
example (st : MiniState MiniMachineData) (r' : MiniRegs)
    (h : r' ≡ₚ st.data.regs except [MiniRegs.Lenses.x3, MiniRegs.Lenses.x4]) :
    { st with data := { st.data with regs := r' } }
      ≡ₚ st except [stX3, stX4] := by
  lens_frame

-- Lens update lifting substate frame
example (st : MiniState MiniMachineData) (r' : MiniRegs)
    (h : r' ≡ₚ (st ^. stRegs) except [MiniRegs.Lenses.x3, MiniRegs.Lenses.x4]) :
    (st & stRegs .~ r') ≡ₚ st except [stX4, stX3, stPc] := by
  lens_frame

-- Substate lifting combined with outer context frame & raw struct equality
example (st₀ st₁ st₂ : MiniState MiniMachineData) (r' : MiniRegs)
    (hSub : r' ≡ₚ st₀.data.regs except [MiniRegs.Lenses.x3, MiniRegs.Lenses.x4])
    (hEq : st₁ = { st₀ with data := { st₀.data with regs := r' } })
    (hPc : st₂ ≡ₚ st₁ except [stPc]) :
    st₂ ≡ₚ st₀ except [stPc, stX3, stX4] := by
  lens_frame

-- Multi-step substate frames lifted through raw struct update
example (st : MiniState MiniMachineData) (r₁ r₂ : MiniRegs)
    (h₁ : r₁ ≡ₚ st.data.regs except [MiniRegs.Lenses.x3])
    (h₂ : r₂ ≡ₚ r₁ except [MiniRegs.Lenses.x4]) :
    { st with data := { st.data with regs := r₂ } }
      ≡ₚ st except [stX3, stX4] := by
  lens_frame

/-! ### 6. Declarative `st is { s₀ with … except … }` Goals -/

example (s₀ : MiniState MiniMachineData) :
    {ₗ s₀ with pc := 16, data.regs.x0 := 1, data.flags.z := true }
      is { s₀ with pc := 16, data.regs.x0 := 1 except data.flags } := by
  lens_frame

-- Reordered concrete updates in `st is { s₀ with … except … }`
example (s₀ : MiniState MiniMachineData) :
    {ₗ s₀ with data.flags.z := true, pc := 16, data.regs.x0 := 1 }
      is { s₀ with pc := 16, data.regs.x0 := 1 except data.flags } := by
  lens_frame

-- Abstract `st` connected via equality hypothesis with reordered updates
example (s₀ st : MiniState MiniMachineData)
    (h : st = {ₗ s₀ with data.flags.z := true, pc := 16, data.regs.x0 := 1 }) :
    st is { s₀ with pc := 16, data.regs.x0 := 1 except data.flags } := by
  lens_frame

-- Abstract `st` connected via context frame hypothesis + coarsening
example (s₀ st : MiniState MiniMachineData)
    (h : st ≡ₚ {ₗ s₀ with pc := 16, data.regs.x0 := 1 } except [stZ]) :
    st is { s₀ with pc := 16, data.regs.x0 := 1 except data.flags } := by
  lens_frame

-- Multi-step equality chain into `st is { s₀ with … except … }`
example (s₀ s₁ st : MiniState MiniMachineData)
    (h₁ : s₁ = {ₗ s₀ with pc := 16 })
    (h₂ : st ≡ₚ {ₗ s₁ with data.regs.x0 := 1 } except [stZ]) :
    st is { s₀ with pc := 16, data.regs.x0 := 1 except data.flags } := by
  lens_frame

/-! ### 7. Engine C: Preservation & Narrowing (`EqOn` / `≡ₚ … on […]`) -/

example (r' r : MiniRegs)
    (h : r' ≡ₚ r except [MiniRegs.Lenses.x3, MiniRegs.Lenses.x4]) :
    r' ≡ₚ r on [MiniRegs.Lenses.sp, MiniRegs.Lenses.x0, MiniRegs.viewA] := by
  lens_frame

-- Derived views on nested state (`stateViewA`, `stateViewMem`) across multi-step context graph
example (st₀ st₁ st₂ : MiniState MiniMachineData) (a₁ a₂ : BitVec 64) (hne : a₁ ≠ a₂)
    (h₁ : st₁ ≡ₚ st₀ except [stPc, stZ])
    (h₂ : st₂ ≡ₚ st₁ except [stX3, stDmem ∘ₗ Lens.atKey a₁]) :
    st₂ ≡ₚ st₀ on [stX0, stateViewA, stateViewMem a₂] := by
  lens_frame

-- Narrowing concrete raw struct update to derived view `stateViewA`
example (s₀ : MiniState MiniMachineData) :
    { s₀ with pc := 16, data := { s₀.data with flags := { s₀.data.flags with z := true } } }
      ≡ₚ s₀ on [stX0, stateViewA] := by
  lens_frame

-- `EqOn` directly (single getter)
example (st₀ st₁ : MiniState MiniMachineData) (a₁ a₂ : BitVec 64) (hne : a₁ ≠ a₂)
    (h : st₁ ≡ₚ st₀ except [stDmem ∘ₗ Lens.atKey a₁, stX0]) :
    EqOn (Getter.of (stateViewMem a₂)) st₁ st₀ := by
  lens_frame

-- Preservation of `stX0High8` when only `stX0Low8` is modified (uses `@[lens_disjoint]`!)
example (st' st : MiniState MiniMachineData)
    (h : st' ≡ₚ st except [stX0Low8]) :
    st' ≡ₚ st on [stX0High8, stPc] := by
  lens_frame

-- Reflexive fast path (`EqOnAll.refl`)
example (st : MiniState MiniMachineData) :
    st ≡ₚ st on [stX0, stateViewA] := by
  lens_frame

-- Narrowing from a larger `EqOnAll` combined with `except`
example (r₀ r₁ r₂ : MiniRegs)
    (h₁ : r₁ ≡ₚ r₀ on [MiniRegs.Lenses.x0, MiniRegs.viewA, MiniRegs.Lenses.sp])
    (h₂ : r₂ ≡ₚ r₁ except [MiniRegs.Lenses.x3]) :
    r₂ ≡ₚ r₀ on [MiniRegs.Lenses.x0, MiniRegs.viewA] := by
  lens_frame

-- Direct context equality on a modified getter closes all getters automatically!
example (r₀ r₁ : MiniRegs)
    (h : r₁ ≡ₚ r₀ except [MiniRegs.Lenses.x3])
    (hx3 : r₁.x3 = r₀.x3) :
    r₁ ≡ₚ r₀ on [MiniRegs.Lenses.x0, MiniRegs.Lenses.x3, MiniRegs.viewA] := by
  lens_frame

-- Partial `EqOnAll`: closes proved getters and leaves ONLY the unproved getter open!
example (r₀ r₁ : MiniRegs)
    (h : r₁ ≡ₚ r₀ except [MiniRegs.Lenses.x3])
    (hx3 : r₁.x3 + 0 = r₀.x3) :
    r₁ ≡ₚ r₀ on [MiniRegs.Lenses.x0, MiniRegs.Lenses.x3, MiniRegs.viewA] := by
  lens_frame
  simpa using hx3

/-! ### 8. Empty Write-Set (`except []`) and Cross-Universe (`PolyState`) -/

example (st : MiniState MiniMachineData) :
    st ≡ₚ st except [] := by
  lens_frame

example (st' st : MiniState MiniMachineData) (h : st' = st) :
    st' ≡ₚ st except [] := by
  lens_frame

example (st₀ st₁ st₂ : MiniState MiniMachineData)
    (h₁ : st₁ ≡ₚ st₀ except [])
    (h₂ : st₂ ≡ₚ st₁ except []) :
    st₂ ≡ₚ st₀ except [] := by
  lens_frame

example (s' s : PolyState)
    (h : s' ≡ₚ s except [PolyState.Lenses.val0]) :
    EqOn PolyState.Lenses.ty1.toGetter s' s := by
  lens_frame

/-! ### 9. Missing-Write UX Diagnostics & Focused Equality Subgoals -/

-- Context equalities on uncovered fields are discharged automatically!
example (s₀ : MiniState MiniMachineData)
    (hx1 : (2 : UInt64) = s₀.data.regs.x1)
    (hpc : (16 : Int64) = s₀.pc) :
    { s₀ with pc := 16, data := { s₀.data with regs := { s₀.data.regs with x0 := 1, x1 := 2 } } }
      ≡ₚ s₀ except [stX0] := by
  lens_frame

/--
info: lens_frame: add to writes: [data.regs.x1, pc]
-/
#guard_msgs in
example (s₀ : MiniState MiniMachineData) :
    { s₀ with
        pc := s₀.pc + 0,
        data := { s₀.data with regs := { s₀.data.regs with x0 := 1, x1 := s₀.data.regs.x1 + 0 } } }
      ≡ₚ s₀ except [stX0] := by
  lens_frame
  · simp
  · simp

/--
info: lens_frame: add to writes: [pc]
-/
#guard_msgs in
example (s₀ : MiniState MiniMachineData) :
    {ₗ s₀ with data.regs.x0 := 1, pc := s₀.pc + 0 } ≡ₚ s₀ except [stX0] := by
  lens_frame
  simp

/--
info: lens_frame: add to writes: [data.regs.x1]
-/
#guard_msgs in
example (s₀ : MiniState MiniMachineData) :
    {ₗ s₀ with data.regs.x1 := s₀.data.regs.x1 + 0, pc := 16, data.regs.x0 := 1 }
      is { s₀ with pc := 16, data.regs.x0 := 1 except data.flags } := by
  lens_frame
  simp

/-! ### 10. Additional Edge Cases (`Prod`, `And`, Single-Pass Lift, `isFrameGoal`, Clean Failure) -/

-- `Prod` constructor diff
example (p : UInt64 × Bool) :
    (p.1, !p.2) ≡ₚ p except [Lens.snd] := by
  lens_frame

-- Conjunction hypothesis unwrapping & chained `let`s
example (s₀ s₁ s₂ : MiniState MiniMachineData)
    (h : (s₁ ≡ₚ s₀ except [stX0]) ∧ (s₂ ≡ₚ s₁ except [stX1])) :
    s₂ ≡ₚ s₀ except [stX1, stX0] := by
  lens_frame

example (s₀ : MiniState MiniMachineData) :
    let s₁ := {ₗ s₀ with pc := 16 }
    let s₂ := {ₗ s₁ with data.regs.x0 := 1 }
    s₂ ≡ₚ s₀ except [stX0, stPc] := by
  lens_frame

-- Single-pass `Modifies.lift` without `LawfulLens` on inner symbolic `atKey` product
example (st : MiniState MiniMachineData) (m' : BitVec 64 → UInt8) (i j : BitVec 64)
    (h : Modifies (Lens.atKey i ×ₗ Lens.atKey j) m' (st ^. stDmem)) :
    Modifies (stDmem ∘ₗ (Lens.atKey i ×ₗ Lens.atKey j)) (st & stDmem .~ m') st := by
  lens_frame

-- Narrowing through a lifted substate frame inside a raw struct update
example (st st' : MiniState MiniMachineData) (r' : MiniRegs)
    (hSub : r' ≡ₚ st.data.regs except [MiniRegs.Lenses.x3, MiniRegs.Lenses.x4])
    (hEq : st' = { st with data := { st.data with regs := r' } }) :
    st' ≡ₚ st on [stX0, stPc, stateViewA] := by
  lens_frame

-- Clean failure when no progress is possible
example (s' s : MiniState MiniMachineData) (h : s' = s) :
    s' ≡ₚ s except [stX0] := by
  have _ : True := by
    fail_if_success
      have : ∀ a b : MiniState MiniMachineData, a ≡ₚ b except [stX0] := fun _ _ => by lens_frame
    trivial
  lens_frame

-- Verify `Optic.Tactic.isFrameGoal` recognition on all 4 frame forms and non-frame goals
section IsFrameGoalCheck
open Lean Meta Elab Command in
#eval show CommandElabM Unit from liftTermElabM do
  let sTy := mkConst ``MiniRegs
  let x0 := mkConst ``MiniRegs.Lenses.x0
  let r₀ ← mkFreshExprMVar sTy
  let r₁ ← mkFreshExprMVar sTy
  let modRel ← mkAppM ``Optic.Modifies #[x0]
  let gRt ← mkAppM ``Optic.ReflTransGen #[modRel, r₁, r₀]
  let gMod ← mkAppM ``Optic.Modifies #[x0, r₁, r₀]
  let gEqOn ← mkAppM ``Optic.EqOn #[← mkAppM ``Optic.Lens.toGetter #[x0], r₁, r₀]
  let nilAny ← mkAppOptM ``List.nil #[some (mkApp (mkConst ``Optic.AnyGetter [Level.zero, Level.zero]) sTy)]
  let gEqOnAll ← mkAppM ``Optic.EqOnAll #[nilAny, r₁, r₀]
  let gEq ← mkEq r₁ r₀
  let gDisj ← mkAppM ``Optic.Disjoint #[x0, mkConst ``MiniRegs.Lenses.x1]
  unless Optic.Tactic.isFrameGoal gRt do throwError "isFrameGoal failed on ReflTransGen (Modifies _)"
  unless Optic.Tactic.isFrameGoal gMod do throwError "isFrameGoal failed on Modifies"
  unless Optic.Tactic.isFrameGoal gEqOn do throwError "isFrameGoal failed on EqOn"
  unless Optic.Tactic.isFrameGoal gEqOnAll do throwError "isFrameGoal failed on EqOnAll"
  if Optic.Tactic.isFrameGoal gEq then throwError "isFrameGoal false positive on Eq"
  if Optic.Tactic.isFrameGoal gDisj then throwError "isFrameGoal false positive on Disjoint"
end IsFrameGoalCheck

end Lens.Tactics.FrameTests
