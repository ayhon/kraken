module

import Lens
import Lens.Tactics.Notation
meta import Lean

/-!
# Tests for `Lens.Tactics.Notation`

Verifies:
1. Dot-path elaboration for `≡ₚ … except […]` (empty, single, multi-field nested paths,
   mixing dot-paths with explicit `Lens` / `Iso` / `Lens.atKey` / local lens expressions,
   and cross-universe structures).
2. Dot-path and view elaboration for `≡ₚ … on […]` (dot-paths, nested dot-path struct views
   like `data.regs.viewA`, struct-namespaced views like `viewA`, qualified views like
   `MiniRegs.viewA`, free views like `stateViewA`, untyped lambdas `fun st => st.pc`, explicit
   `Lens` / `Getter` / `Iso` expressions, and empty `on []`).
3. `st is { s₀ except }`, `st is { s₀ except … }`, and `st is { s₀ with … except … }`.
4. `@[app_unexpander]` pretty-printing for `ReflTransGen (Modifies …)` and `EqOnAll` (both with
   and without `open Optic` / `open scoped Optic.Notation Optic.ProdNotation`, plus fallback safety
   on non-`Modifies` `ReflTransGen`, non-literal `EqOnAll`, and partial applications).
-/

open Optic
open scoped Optic.Notation
open scoped Optic.ProdNotation

namespace Lens.Tactics.NotationTests

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

structure PolyState where
  val0 : UInt64
  ty1 : Type 0

make_lenses MiniRegs
make_lenses MiniFlags
make_lenses MiniMachineData
make_lenses MiniState
make_lenses PolyState

abbrev stRegs : Lens (MiniState MiniMachineData) MiniRegs :=
  MiniState.Lenses.data ∘ₗ MiniMachineData.Lenses.regs

abbrev stDmem : Lens (MiniState MiniMachineData) (BitVec 64 → UInt8) :=
  MiniState.Lenses.data ∘ₗ MiniMachineData.Lenses.dmem

def low8 : Lens (BitVec 64) (BitVec 8) where
  get x := x.extractLsb' 0 8
  set x v := (x &&& ~~~0xFF#64) ||| v.zeroExtend 64

abbrev stX0Low8 : Lens (MiniState MiniMachineData) (BitVec 8) :=
  (stRegs ∘ₗ MiniRegs.Lenses.x0 ∘ₗ Iso.uint64BitVec.toLens) ∘ₗ low8

abbrev MiniRegs.viewA (r : MiniRegs) : Nat := r.x0.toNat + r.x1.toNat
abbrev MiniRegs.viewB (r : MiniRegs) : Nat := r.x3.toNat + r.x4.toNat

def stateViewA (st : MiniState MiniMachineData) : Nat :=
  st.data.regs.x0.toNat + st.data.regs.x1.toNat

def regsSelfIso : Iso MiniRegs MiniRegs := Iso.id

/-! ### 1. Dot-Path Elaboration for `≡ₚ … except […]` -/

-- Pure dot-paths with zero manual `abbrev`s:
theorem dotPathExceptMulti (st' st : MiniState MiniMachineData) :
    (st' ≡ₚ st except [pc, data.regs.x0, data.flags.z]) ↔
      ReflTransGen
        (Modifies (MiniState.Lenses.pc ×ₗ
          ((MiniState.Lenses.data ∘ₗ MiniMachineData.Lenses.regs ∘ₗ MiniRegs.Lenses.x0) ×ₗ
           (MiniState.Lenses.data ∘ₗ MiniMachineData.Lenses.flags ∘ₗ MiniFlags.Lenses.z))))
        st' st :=
  Iff.rfl

-- Concrete 1-line proof using dot-path `except […]`:
example (st : MiniState MiniMachineData) :
    let st' := {ₗ st with pc := 16, data.regs.x0 := 7, data.flags.z := true }
    st' ≡ₚ st except [pc, data.regs.x0, data.flags.z] :=
  ReflTransGen.single ⟨(16, (7, true)), rfl⟩

-- Mixing dot-paths with explicit `Lens` expressions (`stDmem ∘ₗ Lens.atKey a`, `stX0Low8`):
theorem dotPathExceptMixed (st' st : MiniState MiniMachineData) (a : BitVec 64) :
    (st' ≡ₚ st except [pc, stDmem ∘ₗ Lens.atKey a, stX0Low8, data.flags.z]) ↔
      ReflTransGen
        (Modifies (MiniState.Lenses.pc ×ₗ
          ((stDmem ∘ₗ Lens.atKey a) ×ₗ
           (stX0Low8 ×ₗ (MiniState.Lenses.data ∘ₗ MiniMachineData.Lenses.flags ∘ₗ MiniFlags.Lenses.z)))))
        st' st :=
  Iff.rfl

-- Mixing dot-paths with qualified lens constants and bare `Iso` coercion (including polymorphic `Iso.id`):
example (r' r : MiniRegs) :
    (r' ≡ₚ r except [x3, MiniRegs.Lenses.x4, regsSelfIso]) ↔
      ReflTransGen
        (Modifies (MiniRegs.Lenses.x3 ×ₗ (MiniRegs.Lenses.x4 ×ₗ regsSelfIso.toLens)))
        r' r :=
  Iff.rfl

example (r' r : MiniRegs) :
    (r' ≡ₚ r except [Iso.id]) ↔
      ReflTransGen (Modifies (Iso.id (s := MiniRegs)).toLens) r' r :=
  Iff.rfl

-- Interoperability of dot-path `≡ₚ` frames with `lens_indep`:
example (st' st : MiniState MiniMachineData) (a₁ a₂ : BitVec 64) (hne : a₁ ≠ a₂)
    (h : st' ≡ₚ st except [pc, data.regs.x3, stDmem ∘ₗ Lens.atKey a₁]) :
    st' ≡ₚ st on [data.regs.x0, stateViewA, stDmem ∘ₗ Lens.atKey a₂] := by
  refine Modifies.rt_preserves_all ?_ h
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> (dsimp only; lens_indep)

-- Local polymorphic `Lens` variables:
example {S A B : Type} (l₁ : Lens S A) (l₂ : Lens S B) (s' s : S) :
    (s' ≡ₚ s except [l₁, l₂]) ↔ ReflTransGen (Modifies (l₁ ×ₗ l₂)) s' s :=
  Iff.rfl

-- Empty `except []` elaborates to `ReflTransGen (Modifies Lens.unit)`:
theorem dotPathExceptEmpty (st' st : MiniState MiniMachineData) :
    (st' ≡ₚ st except []) ↔ st' = st :=
  Modifies.rt_unit_iff

-- Cross-universe `PolyState`:
example (p' p : PolyState) :
    (p' ≡ₚ p except []) ↔ p' = p :=
  Modifies.rt_unit_iff

example (p' p : PolyState) (h : p' ≡ₚ p except [val0]) : p'.ty1 = p.ty1 :=
  Modifies.rt_preserves (g := PolyState.Lenses.ty1.toGetter) (fun _ _ => rfl) h

-- `st is { s₀ except }`, `st is { s₀ except … }`, and `st is { s₀ with … except … }`:
example (st s₀ : MiniState MiniMachineData) :
    (st is { s₀ except }) ↔ st = s₀ :=
  Modifies.rt_unit_iff

example (st s₀ : MiniState MiniMachineData) :
    (st is { s₀ except pc, data.flags.z }) ↔ (st ≡ₚ s₀ except [pc, data.flags.z]) :=
  Iff.rfl

example (st s₀ : MiniState MiniMachineData)
    (h : st is { s₀ with pc := 16, data.regs.x0 over (· + 1) except data.flags }) :
    st ^. pc = 16 :=
  Modifies.rt_preserves (g := MiniState.Lenses.pc.toGetter) (fun _ _ => rfl) h

/-! ### 2. Dot-Path & View Elaboration for `≡ₚ … on […]` -/

-- Narrowing dot-path `except […]` to dot-path + qualified view `on […]`:
example (r' r : MiniRegs)
    (h : r' ≡ₚ r except [x3, x4]) :
    r' ≡ₚ r on [sp, x0, MiniRegs.viewA] := by
  refine Modifies.rt_preserves_all ?_ h
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> exact fun _ _ => rfl

-- Short struct-namespaced view (`viewA` ↦ `MiniRegs.viewA`) and bare `Iso`:
example (r' r : MiniRegs)
    (h : r' ≡ₚ r except [x3, x4]) :
    r' ≡ₚ r on [sp, x0, viewA] := by
  refine Modifies.rt_preserves_all ?_ h
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> exact fun _ _ => rfl

-- Mixing dot-paths, nested struct view (`data.regs.viewA`), free view (`stateViewA`),
-- untyped lambdas (`fun st => st.pc`, `(·.data.flags.z)`), explicit `Lens` and `Getter`:
example (st' st : MiniState MiniMachineData)
    (h : st' ≡ₚ st except [data.regs.x3, data.flags.n]) :
    st' ≡ₚ st on [pc, data.regs.x0, data.regs.viewA, stateViewA, fun st => st.pc, (·.data.flags.z),
      stX0Low8, Getter.of (fun s : MiniState MiniMachineData => s.data.flags.c)] := by
  refine Modifies.rt_preserves_all ?_ h
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact fun _ _ => rfl

-- Empty `on []`:
example (st' st : MiniState MiniMachineData) : st' ≡ₚ st on [] :=
  EqOnAll.nil st' st

-- Universe-1 field in `on […]`:
example (p' p : PolyState) (h : p' ≡ₚ p except [val0]) : p' ≡ₚ p on [ty1] := by
  refine Modifies.rt_preserves_all ?_ h
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl
  exact fun _ _ => rfl

/-! ### 3. Pretty-Printing Verification (`@[app_unexpander]`) -/

section PrettyPrintTests

def ppExceptMulti (st' st : MiniState MiniMachineData) : Prop :=
  st' ≡ₚ st except [pc, data.regs.x0, data.flags.z]

def ppExceptSingle (st' st : MiniState MiniMachineData) : Prop :=
  st' ≡ₚ st except [pc]

def ppExceptEmpty (st' st : MiniState MiniMachineData) : Prop :=
  st' ≡ₚ st except []

def ppExceptEmptyPoly {S : Type} (s' s : S) : Prop :=
  s' ≡ₚ s except []

def ppExceptEmptyType1 (p' p : PolyState) : Prop :=
  p' ≡ₚ p except []

def ppExceptLeftAssoc (st' st : MiniState MiniMachineData) : Prop :=
  ReflTransGen
    (Modifies (((MiniState.Lenses.pc ×ₗ
        ((MiniState.Lenses.data ∘ₗ MiniMachineData.Lenses.regs) ∘ₗ MiniRegs.Lenses.x0)) ×ₗ
        (MiniState.Lenses.data ∘ₗ (MiniMachineData.Lenses.flags ∘ₗ MiniFlags.Lenses.z)))))
    st' st

def ppExceptMixed (st' st : MiniState MiniMachineData) (a : BitVec 64) : Prop :=
  st' ≡ₚ st except [pc, stDmem ∘ₗ Lens.atKey a, stX0Low8]

def ppOnRegs (r' r : MiniRegs) : Prop :=
  r' ≡ₚ r on [sp, x0, MiniRegs.viewA]

def ppOnRegsShort (r' r : MiniRegs) : Prop :=
  r' ≡ₚ r on [sp, x0, viewA]

def ppOnWrappers (r' r : MiniRegs) : Prop :=
  EqOnAll
    [AnyGetter.of (MiniRegs.Lenses.sp.toGetter),
     AnyGetter.of (Getter.of MiniRegs.viewA),
     AnyGetter.ofIso regsSelfIso]
    r' r

def ppOnState (st' st : MiniState MiniMachineData) : Prop :=
  st' ≡ₚ st on [pc, data.regs.x0, data.regs.viewA, stateViewA, fun st => st.pc]

def ppOnEmpty (st' st : MiniState MiniMachineData) : Prop :=
  st' ≡ₚ st on []

def ppIsWithExcept (st s₀ : MiniState MiniMachineData) : Prop :=
  st is { s₀ with pc := 16 except data.flags }

def ppNonModifiesRT (x y : Nat) : Prop :=
  ReflTransGen Eq x y

def ppNonLiteralEqOnAll (gs : List (AnyGetter MiniRegs)) (r' r : MiniRegs) : Prop :=
  EqOnAll gs r' r

def ppPartialRT : MiniRegs → MiniRegs → Prop :=
  ReflTransGen (Modifies MiniRegs.Lenses.x0)

def ppPartialEqOnAll : MiniRegs → MiniRegs → Prop :=
  EqOnAll [AnyGetter.ofLens MiniRegs.Lenses.x0]

meta section

open Lean Meta PrettyPrinter

private def assertBodyContains (declName : Name) (expectedSubstrings : List String)
    (forbiddenSubstrings : List String := []) : MetaM Unit := do
  let info ← getConstInfo declName
  let some val := info.value? | throwError "declaration `{declName}` has no value"
  let str ← lambdaTelescope val fun _ body => do
    return (← PrettyPrinter.ppExpr body).pretty (width := 200)
  for sub in expectedSubstrings do
    unless (str.splitOn sub).length > 1 do
      throwError "pretty-printing mismatch for `{declName}`:\n  got:      {str}\n  expected substring: {sub}"
  for bad in forbiddenSubstrings do
    if (str.splitOn bad).length > 1 then
      throwError "unexpected substring `{bad}` in pretty-printing of `{declName}`:\n  got: {str}"

#eval show MetaM Unit from do
  assertBodyContains ``ppExceptMulti
    ["st' ≡ₚ st except [pc, data.regs.x0, data.flags.z]"]
    ["ReflTransGen", "Modifies", "Lenses"]
  assertBodyContains ``ppExceptSingle
    ["st' ≡ₚ st except [pc]"]
    ["ReflTransGen", "Modifies", "Lenses"]
  assertBodyContains ``ppExceptEmpty
    ["st' ≡ₚ st except []"]
    ["ReflTransGen", "Modifies", "Lens.unit"]
  assertBodyContains ``ppExceptEmptyPoly
    ["s' ≡ₚ s except []"]
    ["ReflTransGen", "Modifies", "Lens.unit"]
  assertBodyContains ``ppExceptEmptyType1
    ["p' ≡ₚ p except []"]
    ["ReflTransGen", "Modifies", "Lens.unit"]
  assertBodyContains ``ppExceptLeftAssoc
    ["st' ≡ₚ st except [pc, data.regs.x0, data.flags.z]"]
    ["ReflTransGen", "Modifies", "Lenses"]
  assertBodyContains ``ppExceptMixed
    ["st' ≡ₚ st except [pc, stDmem ∘ₗ Lens.atKey a, stX0Low8]"]
    ["ReflTransGen", "Modifies", "Lenses"]
  assertBodyContains ``ppOnRegs
    ["r' ≡ₚ r on [sp, x0, MiniRegs.viewA]"]
    ["EqOnAll", "AnyGetter", "ToAnyGetter", "Lenses"]
  assertBodyContains ``ppOnRegsShort
    ["r' ≡ₚ r on [sp, x0, MiniRegs.viewA]"]
    ["EqOnAll", "AnyGetter", "ToAnyGetter", "Lenses"]
  assertBodyContains ``ppOnWrappers
    ["r' ≡ₚ r on [sp, MiniRegs.viewA, regsSelfIso]"]
    ["EqOnAll", "AnyGetter", "Getter.of", "toGetter", "Lenses"]
  assertBodyContains ``ppOnState
    ["st' ≡ₚ st on [pc, data.regs.x0, data.regs.viewA, stateViewA, fun st => st.pc]"]
    ["EqOnAll", "AnyGetter", "ToAnyGetter", "Lenses"]
  assertBodyContains ``ppOnEmpty
    ["st' ≡ₚ st on []"]
    ["EqOnAll"]
  assertBodyContains ``ppIsWithExcept
    ["st ≡ₚ", "except [data.flags]"]
    ["ReflTransGen", "Modifies", "MiniMachineData.Lenses"]
  assertBodyContains ``ppNonModifiesRT
    ["ReflTransGen Eq x y"]
    ["≡ₚ"]
  assertBodyContains ``ppNonLiteralEqOnAll
    ["EqOnAll gs r' r"]
    ["≡ₚ"]
  assertBodyContains ``ppPartialRT
    ["ReflTransGen"]
    ["≡ₚ"]
  assertBodyContains ``ppPartialEqOnAll
    ["EqOnAll"]
    ["≡ₚ"]

end

end PrettyPrintTests

end Lens.Tactics.NotationTests

/-! ### 4. Pretty-Printing Without `open Optic` / `open scoped Optic.Notation` -/

namespace Lens.Tactics.NotationTestsNoOpen

def ppExceptNoOpen (st' st : Lens.Tactics.NotationTests.MiniState Lens.Tactics.NotationTests.MiniMachineData) : Prop :=
  Optic.ReflTransGen
    (Optic.Modifies
      (Optic.Lens.prod
        Lens.Tactics.NotationTests.MiniState.Lenses.pc
        (Optic.Lens.comp
          (Optic.Lens.comp
            Lens.Tactics.NotationTests.MiniState.Lenses.data
            Lens.Tactics.NotationTests.MiniMachineData.Lenses.regs)
          Lens.Tactics.NotationTests.MiniRegs.Lenses.x0)))
    st' st

def ppOnNoOpen (r' r : Lens.Tactics.NotationTests.MiniRegs) : Prop :=
  Optic.EqOnAll
    [Optic.AnyGetter.ofLens Lens.Tactics.NotationTests.MiniRegs.Lenses.sp,
     Optic.ToAnyGetter.toAnyGetter Lens.Tactics.NotationTests.MiniRegs.viewA]
    r' r

meta section

open Lean Meta PrettyPrinter

#eval show MetaM Unit from do
  for (declName, expected) in [
    (``ppExceptNoOpen, "st' ≡ₚ st except [pc, data.regs.x0]"),
    (``ppOnNoOpen, "r' ≡ₚ r on [sp, NotationTests.MiniRegs.viewA]")
  ] do
    let info ← getConstInfo declName
    let some val := info.value? | throwError "missing value"
    let str ← lambdaTelescope val fun _ body => do
      return (← PrettyPrinter.ppExpr body).pretty (width := 200)
    unless (str.splitOn expected).length > 1 do
      throwError "no-open pretty-printing mismatch for `{declName}`:\n  got:      {str}\n  expected: {expected}"

end

end Lens.Tactics.NotationTestsNoOpen
