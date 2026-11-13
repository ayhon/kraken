module

import all Kraken.X64.Examples.Examples
import Kraken.Tactics

/-!
# x86-64 Composition and Frame Tactic Tests

Regression tests for `block_spec`, `kcall`, `kframe`, and constant-time composition on x86-64.
-/

open Kraken Kraken.X64
open Kraken.X64.Parser
open Std.ExtHashMap

/-- Finish-block specification with a `(writes := [rax])` register frame. -/
block_spec swap_and_add_finish_frame_spec swap_and_add s
  from "finish"
  (writes := [rax])
  (post := fun st =>
    st.data.regs.rax = s.regs.rax + s.regs.rcx ∧
    st.data.dmem = s.dmem) := by
  kprologue swap_and_add at "finish" with s
  kfinish swap_and_add

/-- Untraced composition of `swap_mem_block_spec` (`step1_subprog`) with `swap_and_add_finish_frame_spec` (`kcall`),
narrowing to `(preserves := [rdi, rsi])`. -/
block_spec swap_and_add_correct' swap_and_add s₀ (x y : UInt64) (R : DataMem → Prop)
  (preserves := [rdi, rsi])
  (pre :=
    s₀.dmem =⋆ x @ s₀.regs.rdi ⋆ y @ s₀.regs.rsi ⋆ R)
  (post := fun st =>
    st.data.regs.rax = x.toBitVec + y.toBitVec ∧
    (st.data.dmem =⋆ y @ s₀.regs.rdi ⋆ x @ s₀.regs.rsi ⋆ R)) := by
  intro h_mem
  refine step1_subprog 0 (swap_mem_block_spec s₀ x y R) h_mem (by rfl) (by kaddr swap_and_add) ?_
  rintro s₁ ⟨h_rax, h_rcx, h_rdi₁, h_rsi₁, h_mem₁⟩
  kcall swap_and_add_finish_frame_spec s₁ with s₂ ⟨h_fr₂, h_rax₂, h_dmem₂⟩
  kframe_eqs h_fr₂
  dsimp only at h_rdi₁ h_rsi₁
  apply Eventually.done
  refine ⟨by kframe <;> grind, by grind, h_dmem₂ ▸ h_mem₁⟩

/-- Constant-time traced composition of `swap_mem_block_ct_spec` with `swap_and_add_finish_ct_spec`. -/
block_spec swap_and_add_ct_correct' swap_and_add (x_ptr y_ptr : BitVec 64)
    s₀ (x y : UInt64) (R : DataMem → Prop) ct
  (pre :=
    s₀.regs.rdi = x_ptr ∧ s₀.regs.rsi = y_ptr ∧
    (s₀.dmem =⋆ x @ x_ptr ⋆ y @ y_ptr ⋆ R))
  (post := fun st =>
    st.data.regs.rax = x.toBitVec + y.toBitVec ∧
    (st.data.dmem =⋆ y @ x_ptr ⋆ x @ y_ptr ⋆ R)) := by
  kintro s₀ x y R ⟨h_rdi, h_rsi, h_mem⟩
  refine step1_subprog_traced 0 ((swap_mem_block_ct_spec x_ptr y_ptr).choose_spec s₀ x y R)
    ⟨h_rdi, h_rsi, h_mem⟩ (by rfl) (by kaddr swap_and_add) ?_
  rintro s₁ ⟨h_rax, h_rcx, -, -, h_mem₁⟩
  kcall swap_and_add_finish_ct_spec.choose_spec s₁ with s₂ ⟨h_rax₂, h_dmem₂⟩
  kdone
  exact ⟨by grind, h_dmem₂ ▸ h_mem₁⟩

