module

import Lens
import Lens.Tactics.Eqs
import Lean

/-!
# Tests for `Lens.Tactics.Eqs` (`lens_eqs`, `lens_rw`, `frameEqsFor`, `frameEqsInContext`)

Exercises:
1. Demand-driven `lens_eqs h` (only referenced fields/views extracted — unreferenced fields omitted).
2. Explicit targeted `lens_eqs h [p₁, p₂, …]` with dot-paths, explicit lenses, and derived views.
3. `st is { s₀ with pc := 16, data.regs.x0 over (· + 1) except data.flags }` RHS normalization
   (producing `st.pc = 16`, `st.data.regs.x0 = s₀.data.regs.x0 + 1`, `st.data.dmem = s₀.data.dmem`)
   and `st is { s₀ with … }` without `except`.
4. Outermost-preserved-prefix collapsing (whole-map `dmem` collapsing and `regs` subsumption).
5. `lens_eqs h` on `EqOnAll` (`≡ₚ … on […]`) and `EqOn`.
6. Symbolic aliasing `Lens.atKey i ×ₗ Lens.atKey j` preserving `m₃ k = m₀ k` (`k ≠ i`, `k ≠ j`).
7. `lens_rw` on multi-hop chains `s₂ → s₁ → s₀`, `lens_rw at h`, `lens_rw at *`, cycle safety,
   and `is { … with … except … }` chaining without adding hypotheses to the local context.
8. Failure diagnostics naming the conflicting write lens when extracting a modified field.
9. Direct `MetaM` / `TacticM` API checks (`parseFrameHyp?`, `findConflictingWriteLens?`,
   `frameEqsFor`, `frameEqsInContext`).
-/

open Optic
open scoped Optic.Notation
open scoped Optic.ProdNotation

namespace Lens.Tactics.EqsTests

/-! ### Standalone Test State Hierarchy (Zero Dependencies on `Kraken/`) -/

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

abbrev stX3 : Lens (MiniState MiniMachineData) UInt64 :=
  stRegs ∘ₗ MiniRegs.Lenses.x3

abbrev stX4 : Lens (MiniState MiniMachineData) UInt64 :=
  stRegs ∘ₗ MiniRegs.Lenses.x4

abbrev stSp : Lens (MiniState MiniMachineData) UInt64 :=
  stRegs ∘ₗ MiniRegs.Lenses.sp

abbrev stZ : Lens (MiniState MiniMachineData) Bool :=
  stFlags ∘ₗ MiniFlags.Lenses.z

abbrev stPc : Lens (MiniState MiniMachineData) Int64 :=
  MiniState.Lenses.pc

abbrev MiniRegs.viewA (r : MiniRegs) : Nat :=
  r.x0.toNat + r.x1.toNat

def stateViewA (st : MiniState MiniMachineData) : Nat :=
  st.data.regs.x0.toNat + st.data.regs.x1.toNat

def stateViewMem (addr : BitVec 64) (st : MiniState MiniMachineData) : Nat :=
  st.data.regs.sp.toNat + (st.data.dmem addr).toNat

/-! ### 1. Demand-Driven `lens_eqs h` (Only Referenced Fields/Views Extracted) -/

example (s₀ st : MiniState MiniMachineData)
    (h : st ≡ₚ s₀ except [stX3, stZ]) :
    st.data.regs.x0 = s₀.data.regs.x0 ∧ stateViewA st = stateViewA s₀ := by
  lens_eqs h
  -- Only referenced fields/views (`h_x0`, `h_stateViewA`) should be asserted, NOT unreferenced `h_pc` or `h_x2`:
  run_tac Lean.Elab.Tactic.withMainContext do
    let lctx ← Lean.getLCtx
    unless (lctx.findFromUserName? `h_x0).isSome do Lean.throwError "missing h_x0"
    unless (lctx.findFromUserName? `h_stateViewA).isSome do Lean.throwError "missing h_stateViewA"
    unless (lctx.findFromUserName? `h_pc).isNone do Lean.throwError "unexpected h_pc"
    unless (lctx.findFromUserName? `h_x2).isNone do Lean.throwError "unexpected h_x2"
    unless (lctx.findFromUserName? `h_dmem).isNone do Lean.throwError "unexpected h_dmem"
  exact ⟨h_x0, h_stateViewA⟩

-- Also extracts fields referenced only in context hypotheses:
example (s₀ st : MiniState MiniMachineData) (a₁ a₂ : BitVec 64) (hne : a₁ ≠ a₂)
    (h : st ≡ₚ s₀ except [stDmem ∘ₗ Lens.atKey a₁, stX3])
    (hpre : stateViewMem a₂ st = 99) :
    stateViewMem a₂ s₀ = 99 := by
  lens_eqs h
  rw [← h_stateViewMem]
  exact hpre

/-! ### 2. Explicit Targeted `lens_eqs h [p₁, p₂, …]` -/

example (s₀ st : MiniState MiniMachineData) (a₁ a₂ : BitVec 64) (hne : a₁ ≠ a₂)
    (h : st ≡ₚ s₀ except [stX3, stDmem ∘ₗ Lens.atKey a₁]) :
    st.data.regs.x0 = s₀.data.regs.x0 ∧
      st.pc = s₀.pc ∧
      stateViewA st = stateViewA s₀ ∧
      stateViewMem a₂ st = stateViewMem a₂ s₀ := by
  lens_eqs h [data.regs.x0, pc, stateViewA, stateViewMem a₂]
  exact ⟨h_x0, h_pc, h_stateViewA, h_stateViewMem⟩

-- Explicit `Lens` and composed `atKey` lens expressions in `[...]`:
example (s₀ st : MiniState MiniMachineData) (a₁ a₂ : BitVec 64) (hne : a₁ ≠ a₂)
    (h : st ≡ₚ s₀ except [stX3, stDmem ∘ₗ Lens.atKey a₁]) :
    st.data.regs.x0 = s₀.data.regs.x0 ∧ st.data.dmem a₂ = s₀.data.dmem a₂ := by
  lens_eqs h [stX0, stDmem ∘ₗ Lens.atKey a₂]
  exact ⟨h_x0, h_dmem_a₂⟩

/-! ### 3. `st is { s₀ with … except … }` RHS Normalization -/

example (s₀ st : MiniState MiniMachineData)
    (h : st is { s₀ with pc := 16, data.regs.x0 over (· + 1) except data.flags }) :
    st.pc = 16 ∧ st.data.regs.x0 = s₀.data.regs.x0 + 1 ∧ st.data.dmem = s₀.data.dmem := by
  lens_eqs h
  exact ⟨h_pc, h_x0, h_dmem⟩

-- Also works with explicit targets and untouched fields (`data.regs.x1`):
example (s₀ st : MiniState MiniMachineData)
    (h : st is { s₀ with pc := 16, data.regs.x0 over (· + 1) except data.flags }) :
    st.pc = 16 ∧ st.data.regs.x0 = s₀.data.regs.x0 + 1 ∧
      st.data.regs.x1 = s₀.data.regs.x1 ∧ st.data.dmem = s₀.data.dmem := by
  lens_eqs h [pc, data.regs.x0, data.regs.x1, data.dmem]
  exact ⟨h_pc, h_x0, h_x1, h_dmem⟩

-- Also works on `st is { s₀ with … }` without `except`:
example (s₀ st : MiniState MiniMachineData)
    (h : st is { s₀ with pc := 16, data.regs.x0 over (· + 1) }) :
    st.pc = 16 ∧ st.data.regs.x0 = s₀.data.regs.x0 + 1 ∧ st.data.dmem = s₀.data.dmem := by
  lens_eqs h
  exact ⟨h_pc, h_x0, h_dmem⟩

/-! ### 4. Outermost-Preserved-Prefix Collapsing -/

-- Whole-map collapsing: referencing `dmem a₁` and `dmem a₂` when `dmem` is untouched emits ONE `h_dmem`:
example (s₀ st : MiniState MiniMachineData) (a₁ a₂ : BitVec 64)
    (h : st ≡ₚ s₀ except [stPc, stX3]) :
    st.data.dmem a₁ = s₀.data.dmem a₁ ∧ st.data.dmem a₂ = s₀.data.dmem a₂ := by
  lens_eqs h
  run_tac Lean.Elab.Tactic.withMainContext do
    let lctx ← Lean.getLCtx
    unless (lctx.findFromUserName? `h_dmem).isSome do Lean.throwError "missing h_dmem"
    unless (lctx.findFromUserName? `h_dmem_a₁).isNone do Lean.throwError "unexpected h_dmem_a₁"
    unless (lctx.findFromUserName? `h_dmem_a₂).isNone do Lean.throwError "unexpected h_dmem_a₂"
  rw [h_dmem]
  exact ⟨rfl, rfl⟩

-- Outermost-preserved-prefix collapsing: when BOTH `st.data.regs` and `st.data.regs.x0` appear and
-- `regs` is preserved as a whole, emit only `h_regs`:
example (s₀ st : MiniState MiniMachineData)
    (h : st ≡ₚ s₀ except [stPc, stZ]) :
    st.data.regs = s₀.data.regs ∧ st.data.regs.x0 = s₀.data.regs.x0 := by
  lens_eqs h
  run_tac Lean.Elab.Tactic.withMainContext do
    let lctx ← Lean.getLCtx
    unless (lctx.findFromUserName? `h_regs).isSome do Lean.throwError "missing h_regs"
    unless (lctx.findFromUserName? `h_x0).isNone do Lean.throwError "unexpected h_x0"
  rw [h_regs]
  exact ⟨rfl, rfl⟩

/-! ### 5. `EqOnAll` (`≡ₚ … on […]`) and `EqOn` -/

example (r' r : MiniRegs)
    (h : r' ≡ₚ r on [MiniRegs.Lenses.sp, MiniRegs.Lenses.x0, MiniRegs.viewA]) :
    r'.x0 = r.x0 ∧ MiniRegs.viewA r' = MiniRegs.viewA r := by
  lens_eqs h
  run_tac Lean.Elab.Tactic.withMainContext do
    let lctx ← Lean.getLCtx
    unless (lctx.findFromUserName? `h_x0).isSome do Lean.throwError "missing h_x0"
    unless (lctx.findFromUserName? `h_viewA).isSome do Lean.throwError "missing h_viewA"
    unless (lctx.findFromUserName? `h_sp).isNone do Lean.throwError "unexpected h_sp"
  exact ⟨h_x0, h_viewA⟩

example (s₀ st : MiniState MiniMachineData)
    (h : EqOn stRegs.toGetter st s₀) :
    st.data.regs.x0 = s₀.data.regs.x0 := by
  lens_eqs h
  exact h_x0

/-! ### 6. Symbolic Aliasing (`atKey i ×ₗ atKey j`) -/

example (m₀ m₃ : BitVec 64 → UInt8) (i j k : BitVec 64)
    (hki : k ≠ i) (hkj : k ≠ j)
    (h : m₃ ≡ₚ m₀ except [Lens.atKey i, Lens.atKey j]) :
    m₃ k = m₀ k := by
  lens_eqs h
  exact h_k

/-! ### 7. Demand-Driven `lens_rw` (Multi-Hop Chains, `at *`, Cycle Safety, Zero Context Pollution) -/

-- Multi-hop chain `s₂ → s₁ → s₀` rewritten in one sweep without adding hypotheses to context:
example (s₀ s₁ s₂ : MiniState MiniMachineData)
    (h₁ : s₁ ≡ₚ s₀ except [stX3])
    (h₂ : s₂ ≡ₚ s₁ except [stX4, stZ]) :
    s₂.data.regs.x0 = s₀.data.regs.x0 ∧
      stateViewA s₂ = stateViewA s₀ ∧
      s₂.pc = s₀.pc := by
  run_tac do
    let nBefore ← Lean.Elab.Tactic.withMainContext do return (← Lean.getLCtx).size
    Lean.Elab.Tactic.evalTactic (← `(tactic| lens_rw))
    let nAfter ← Lean.Elab.Tactic.withMainContext do return (← Lean.getLCtx).size
    unless nBefore == nAfter do
      Lean.throwError "lens_rw polluted local context: {nBefore} → {nAfter}"
  exact ⟨rfl, rfl, rfl⟩

-- Single equality closes directly with `lens_rw` (just like `rw`):
example (s₀ s₁ s₂ : MiniState MiniMachineData) (a₁ a₂ : BitVec 64) (hne : a₁ ≠ a₂)
    (h₁ : s₁ ≡ₚ s₀ except [stDmem ∘ₗ Lens.atKey a₁])
    (h₂ : s₂ ≡ₚ s₁ except [stX4]) :
    s₂.data.dmem a₂ = s₀.data.dmem a₂ := by
  lens_rw

-- `lens_rw at h₁ h₂` and `lens_rw at *` rewrite hypotheses in place without polluting context:
example (s₀ s₁ s₂ : MiniState MiniMachineData)
    (h₁ : s₁ ≡ₚ s₀ except [stX3])
    (h₂ : s₂ ≡ₚ s₁ except [stX4])
    (hx : s₂.data.regs.x0 = 42)
    (hv : stateViewA s₂ = 100) :
    s₀.data.regs.x0 = 42 ∧ stateViewA s₀ = 100 := by
  lens_rw at hx hv
  exact ⟨hx, hv⟩

example (s₀ s₁ s₂ : MiniState MiniMachineData)
    (h₁ : s₁ ≡ₚ s₀ except [stX3])
    (h₂ : s₂ ≡ₚ s₁ except [stX4])
    (hx : s₁.data.regs.x0 = 42) :
    s₂.data.regs.x0 = 42 := by
  lens_rw at *
  exact hx

-- Multi-hop `is { … with … except … }` chaining in `lens_rw`:
example (s₀ s₁ s₂ : MiniState MiniMachineData)
    (h₁ : s₁ is { s₀ with pc := 16, data.regs.x0 over (· + 1) except data.flags })
    (h₂ : s₂ is { s₁ with pc over (· + 4) except data.flags }) :
    s₂.pc = 16 + 4 ∧ s₂.data.regs.x0 = s₀.data.regs.x0 + 1 ∧ s₂.data.dmem = s₀.data.dmem := by
  lens_rw
  exact ⟨rfl, rfl, rfl⟩

-- Cycle safety: symmetric 2-cycle and 3-cycle frame hypotheses in context do not loop:
example (s₀ s₁ : MiniState MiniMachineData)
    (h₁ : s₁ ≡ₚ s₀ except [stX3])
    (_h₂ : s₀ ≡ₚ s₁ except [stX3]) :
    s₁.data.regs.x0 = s₀.data.regs.x0 := by
  lens_rw

example (s₀ s₁ s₂ : MiniState MiniMachineData)
    (h₁ : s₁ ≡ₚ s₀ except [stX3])
    (h₂ : s₂ ≡ₚ s₁ except [stX4])
    (_h₃ : s₀ ≡ₚ s₂ except [stPc]) :
    s₂.data.regs.x0 = s₀.data.regs.x0 := by
  lens_rw

-- `lens_rw` with `^.` notation and nested map-key rewrite enabled by post-order pass:
example (s₀ s₁ s₂ : MiniState MiniMachineData) (a₁ : BitVec 64)
    (h₁ : s₁ ≡ₚ s₀ except [stDmem ∘ₗ Lens.atKey a₁])
    (h₂ : s₂ ≡ₚ s₁ except [stX4])
    (hne : a₁ ≠ s₀.data.regs.x0.toBitVec) :
    (s₂ ^. pc) = (s₀ ^. pc) ∧
      s₂.data.dmem (s₂.data.regs.x0.toBitVec) = s₀.data.dmem (s₀.data.regs.x0.toBitVec) := by
  lens_rw
  exact ⟨rfl, rfl⟩

/-! ### 8. Additional Edge Cases (`Modifies`, `ModifiesAny`, Binders, Prefix `with`, `Iso`/`Getter`) -/

-- Bare `lens_eqs` across multiple frame hypotheses:
example (s₀ s₁ s₂ : MiniState MiniMachineData)
    (h₁ : s₁ ≡ₚ s₀ except [stX3])
    (h₂ : s₂ ≡ₚ s₁ except [stX4]) :
    s₂.data.regs.x0 = s₀.data.regs.x0 := by
  lens_eqs
  exact h₂_x0.trans h₁_x0

-- Single-pass `Modifies` and baseline `ModifiesAny` (`≡ₗ … except […]`):
example (s₀ st : MiniState MiniMachineData)
    (h : Modifies stX3 st s₀) :
    st.data.regs.x0 = s₀.data.regs.x0 := by
  lens_eqs h
  exact h_x0

example (s₀ st : MiniState MiniMachineData)
    (h : st ≡ₗ s₀ except [stX3, stZ]) :
    st.data.regs.x0 = s₀.data.regs.x0 ∧ stateViewA st = stateViewA s₀ := by
  lens_eqs h
  exact ⟨h_x0, h_stateViewA⟩

-- Outer struct set in `with` (`data.regs := rNew`) projects cleanly to inner field (`st.data.regs.x0 = rNew.x0`):
example (s₀ st : MiniState MiniMachineData) (rNew : MiniRegs)
    (h : st is { s₀ with data.regs := rNew except data.flags }) :
    st.data.regs.x0 = rNew.x0 ∧ st.pc = s₀.pc := by
  lens_eqs h
  exact ⟨h_x0, h_pc⟩

-- Bound variables under `∀`: still extracts whole-map `h_dmem` without failing on local binders:
example (s₀ st : MiniState MiniMachineData)
    (h : st ≡ₚ s₀ except [stPc, stX3]) :
    ∀ a : BitVec 64, st.data.dmem a = s₀.data.dmem a := by
  lens_eqs h
  intro a
  rw [h_dmem]

-- Explicit `Getter` and `Iso` targets in `lens_eqs h […]`:
example (r₀ r : MiniRegs)
    (h : r ≡ₚ r₀ except [MiniRegs.Lenses.x3]) :
    MiniRegs.viewA r = MiniRegs.viewA r₀ ∧ r.x0 = r₀.x0 := by
  lens_eqs h [Getter.of MiniRegs.viewA, MiniRegs.Lenses.x0]
  exact ⟨h_viewA, h_x0⟩

example (x₀ x : UInt64)
    (h : x ≡ₚ x₀ except []) :
    Iso.uint64BitVec.to x = Iso.uint64BitVec.to x₀ := by
  lens_eqs h [Iso.uint64BitVec]
  exact h_uint64BitVec

-- `EqOnAll` fallback when goal does not directly mention fields of `r'`:
set_option linter.unusedVariables false in
example (r' r : MiniRegs)
    (h : r' ≡ₚ r on [MiniRegs.Lenses.x0, MiniRegs.viewA]) : True := by
  lens_eqs h
  run_tac Lean.Elab.Tactic.withMainContext do
    let lctx ← Lean.getLCtx
    unless (lctx.findFromUserName? `h_x0).isSome do Lean.throwError "missing fallback h_x0"
    unless (lctx.findFromUserName? `h_viewA).isSome do Lean.throwError "missing fallback h_viewA"
  trivial

/-! ### 9. Failure Diagnostics Naming the Conflicting Write Lens -/

set_option linter.unusedVariables false in
example (s₀ st : MiniState MiniMachineData)
    (h : st ≡ₚ s₀ except [stPc, stX3, stZ]) : True := by
  run_tac Lean.Elab.Tactic.withMainContext do
    let hId := Lean.mkIdent `h
    let pId := Lean.mkIdent `data.regs.x3
    let mut errMsg := ""
    try
      Lean.Elab.Tactic.evalTactic (← `(tactic| lens_eqs $hId [$pId]))
    catch e =>
      errMsg ← e.toMessageData.toString
    unless !errMsg.isEmpty do
      Lean.throwError "expected lens_eqs to fail on modified field data.regs.x3"
    unless (errMsg.splitOn "conflicts with write lens").length > 1 do
      Lean.throwError "error message did not mention conflicting write lens: {errMsg}"
    unless (errMsg.splitOn "x3").length > 1 do
      Lean.throwError "error message did not name conflicting lens x3: {errMsg}"
  trivial

/-! ### 10. Direct `MetaM` / `TacticM` API Verification -/

example (s₀ st : MiniState MiniMachineData)
    (h : st ≡ₚ s₀ except [stPc, stX3]) :
    st.data.regs.x0 = s₀.data.regs.x0 := by
  run_tac Lean.Elab.Tactic.withMainContext do
    let hyps ← Optic.Tactic.collectFrameHyps
    unless hyps.size == 1 do Lean.throwError "expected 1 frame hyp, got {hyps.size}"
    let eqs ← Optic.Tactic.frameEqsInContext
    unless eqs.size == 1 do Lean.throwError "expected 1 frame eq, got {eqs.size}"
    let conflict? ← Optic.Tactic.findConflictingWriteLens?
      (← Lean.Elab.Term.elabTerm (← `(stPc ×ₗ stX3)) none)
      (← Lean.Elab.Term.elabTerm (← `(stX3.toGetter)) none)
    unless conflict?.isSome do Lean.throwError "expected conflicting write lens"
  lens_rw

end Lens.Tactics.EqsTests
