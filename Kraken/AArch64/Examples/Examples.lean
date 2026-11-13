module

import Kraken.AArch64.Parser
import Kraken.AArch64.Semantics
import Kraken.BitVecArith
import Kraken.Eval
import Kraken.SeparationMem
import Kraken.SeparationTactics
import Kraken.Tactics
import Kraken.ToBytes

/-!
# AArch64 Example Programs

Example AArch64 assembly programs and correctness proofs demonstrating register arithmetic,
control flow, memory addressing modes, function pointers, and jump tables.
-/

open Kraken.AArch64
open Kraken.AArch64.Parser
open Std
open Std.ExtHashMap

/-! ### Register and Control-Flow Examples -/

/-- Register swap using `eor`. -/
def swap : Program := ⸨prog|
  eor x0, x0, x1
  eor x1, x0, x1
  eor x0, x0, x1
⸩

theorem swap_correct [layout : Host swap] (d : MachineData) :
    (layout swap).Spec d
      (post := fun st =>
        st.data.regs.getRegOrZr .X0 = d.regs.getRegOrZr .X1 ∧
        st.data.regs.getRegOrZr .X1 = d.regs.getRegOrZr .X0) := by
  kprologue swap with d
  kfinish swap

/-- Multi-instruction arithmetic and shift pipeline. -/
def arith_shift : Program := ⸨prog|
  add x0, x1, #42
  lsl x2, x0, #2
  sub x3, x2, x0
⸩

theorem arith_shift_correct [layout : Host arith_shift] (d : MachineData) :
    (layout arith_shift).Spec d
      (post := fun st =>
        st.data.regs.getRegOrZr .X3 = 3 * (d.regs.getRegOrZr .X1 + 42)) := by
  kprologue arith_shift with d
  kfinish arith_shift

/-- Stepping through conditional branch (`cbnz` not taken). -/
def controlflow : Program := ⸨prog|
start:
  mov x0, #1
  eor x0, x0, x0
  cbnz x0, start
  mov x1, #42
⸩

theorem p4_correct [layout : Host controlflow] (d : MachineData) :
    (layout controlflow).Spec d (post := fun st => st.data.regs.X1 = 42) := by
  kprologue controlflow with d
  kfinish controlflow

/-! ### Memory Addressing Examples -/

/-- Storing and loading 64-bit registers with immediate byte offsets. -/
def move_2_regs_to_heap : Program := ⸨prog|
    str x0, [x2]
    str x1, [x2, #8]
    ldr x3, [x2]
    ldr x4, [x2, #8]
⸩

theorem move_2_regs_to_heap_correct [layout : Host move_2_regs_to_heap] (s₀ : MachineData)
    (v1 v2 : UInt64) (R : DataMem → Prop) :
    (layout move_2_regs_to_heap).Spec s₀
      (pre :=
        s₀.dmem =⋆ v1 @ s₀.regs.X2 ⋆ v2 @ s₀.regs.X2 + 8 ⋆ R)
      (post := fun st =>
        st.data.regs.X3 = s₀.regs.X0 ∧
        st.data.regs.X4 = s₀.regs.X1 ∧
        st.data.regs.X2 = s₀.regs.X2) := by
  kprologue move_2_regs_to_heap with s₀
  kfinish move_2_regs_to_heap

/-- Memory access with shifted register offset `[x1, x2, lsl #3]`. -/
def reg_offset_example : Program := ⸨prog|
    mov x0, #42
    str x0, [x1, x2, lsl #3]
    mov x0, #0
    ldr x3, [x1, x2, lsl #3]
⸩

theorem reg_offset_example_correct [layout : Host reg_offset_example] (s₀ : MachineData)
    (v : UInt64) (R : DataMem → Prop) :
    (layout reg_offset_example).Spec s₀
      (pre :=
        s₀.dmem =⋆ v @ s₀.regs.X1.toBitVec + BitVec.ofInt 64 (s₀.regs.X2.toBitVec.toNat <<< 3) ⋆ R)
      (post := fun st => st.data.regs.X3 = 42) := by
  kprologue reg_offset_example with s₀
  kfinish reg_offset_example

/-! ### Function Pointers and Jump Tables -/

/-- Materializing a subroutine's address with `adr`, calling it indirectly with `blr`, and returning with `ret`. -/
def fn_ptr_call : Program := ⸨prog|
  adr x2, add_ten
  blr x2
  b done
add_ten:
  add x0, x0, #10
  ret
done:
  nop
⸩

theorem fn_ptr_call_correct [layout : Host fn_ptr_call] (s₀ : MachineData) :
    (layout fn_ptr_call).Spec s₀
      (post := fun st => st.data.regs.X0 = s₀.regs.X0 + 10) := by
  kprologue fn_ptr_call to "add_ten" with s₀
  kstep
  simp +zetaDelta only [BitVec.ofInt_toInt, Int64.ofInt_bitVecToInt]
  kprologue fn_ptr_call at "add_ten"
  kstep
  simp +zetaDelta only [Int64.ofInt_bitVecToInt]
  kprologue fn_ptr_call at 2
  kfinish fn_ptr_call

/-- Higher-order caller that invokes a callback at `fn_ptr` via `blr x2` and increments its return value. -/
def apply_callback : Program := ⸨prog|
  blr x2
  add x0, x0, #1
⸩

theorem apply_callback_correct [layout : Host apply_callback] (s₀ : MachineData)
    (fn_ptr : Int64) (f : UInt64 → UInt64)
    (h_cb : ∀ s : MachineData,
      (layout apply_callback).Spec s
        (pc := fn_ptr)
        (post := fun st =>
          st.pc = Int64.ofInt s.regs.X30.toBitVec.toInt ∧
          st.data.regs.X0 = f s.regs.X0)) :
    (layout apply_callback).Spec s₀
      (pre := Int64.ofInt s₀.regs.X2.toBitVec.toInt = fn_ptr)
      (post := fun st => st.data.regs.X0 = f s₀.regs.X0 + 1) := by
  intro h_fn
  kprologue apply_callback take 1 with s₀
  kstep
  dsimp +zetaDelta only
  rw [h_fn]
  kcall h_cb _ with s₁ h_x0
  simp +zetaDelta only [BitVec.ofInt_toInt, Int64.ofInt_bitVecToInt]
  kprologue apply_callback at 1
  kfinish apply_callback

/-- 3-way jump-table dispatch (`adrp` + `:lo12:` page-offset address materialization +
shifted-register `ldr` + `br`). -/
def jump_table : Program := ⸨prog|
  adrp x2, .Ltable
  add x2, x2, :lo12:.Ltable
  ldr x3, [x2, x0, lsl #3]
  br x3
.Lcase0:
  mov x0, #10
  b .Ldone
.Lcase1:
  mov x0, #20
  b .Ldone
.Lcase2:
  mov x0, #30
  b .Ldone
.Ltable:
.Ldone:
  nop
⸩

theorem jump_table_correct [layout : Host jump_table] (s₀ : MachineData) (R : DataMem → Prop) :
    (layout jump_table).Spec s₀
      (pre :=
        let tbl := ((layout jump_table).label ".Ltable").toBitVec
        let c0 := UInt64.ofBitVec ((layout jump_table).label ".Lcase0").toBitVec
        let c1 := UInt64.ofBitVec ((layout jump_table).label ".Lcase1").toBitVec
        let c2 := UInt64.ofBitVec ((layout jump_table).label ".Lcase2").toBitVec
        s₀.regs.X0.toNat < 3 ∧
        (s₀.dmem =⋆ c0 @ tbl ⋆ c1 @ (tbl + 8#64) ⋆ c2 @ (tbl + 16#64) ⋆ R))
      (post := fun st =>
        st.data.regs.X0 = match s₀.regs.X0.toNat with | 0 => 10 | 1 => 20 | _ => 30) := by
  rintro ⟨h_idx, h_mem⟩
  have h_cases : s₀.regs.X0 = 0 ∨ s₀.regs.X0 = 1 ∨ s₀.regs.X0 = 2 := by
    rcases (show s₀.regs.X0.toNat = 0 ∨ s₀.regs.X0.toNat = 1 ∨ s₀.regs.X0.toNat = 2 by omega) with h | h | h
    · left; exact UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (by simp [h]))
    · right; left; exact UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (by simp [h]))
    · right; right; exact UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (by simp [h]))
  rcases h_cases with h0 | h1 | h2
  · kprologue jump_table to ".Lcase0" with s₀
    subst h0
    kstep
    simp +zetaDelta only [Int64.ofInt_bitVecToInt]
    kprologue jump_table at ".Lcase0"
    kfinish jump_table
  · kprologue jump_table to ".Lcase0" with s₀
    subst h1
    kstep
    simp +zetaDelta only [Int64.ofInt_bitVecToInt]
    kprologue jump_table at ".Lcase1"
    kfinish jump_table
  · kprologue jump_table to ".Lcase0" with s₀
    subst h2
    kstep
    simp +zetaDelta only [Int64.ofInt_bitVecToInt]
    kprologue jump_table at ".Lcase2"
    kfinish jump_table
