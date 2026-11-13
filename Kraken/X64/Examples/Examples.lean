module

import Kraken.Eval
import Kraken.SeparationMem
import Kraken.SeparationTactics
import Kraken.Tactics
import Kraken.X64.Parser
import Kraken.X64.PrettyPrint
import Kraken.X64.Semantics
meta import Kraken.X64.Semantics

/-!
# x86-64 Example Programs

Example x86-64 assembly programs and correctness proofs demonstrating straight-line
symbolic execution, memory and stack addressing, loops, composable block specifications,
function pointers, and jump tables.
-/

open Kraken.X64.Parser
open Std
open Std.ExtHashMap

/-! ### Straight-Line Register and Control-Flow Examples -/

def p1 := ⸨prog| start: mov $1, %rax ⸩

example [layout : Host p1] (s : MachineData) :
    (layout p1).Spec s (post := fun st => st.data.regs.rax = 1) := by
  kprologue p1 with s
  kfinish p1

def swap : Program := ⸨prog|
  xor %rbx, %rax
  xor %rax, %rbx
  xor %rbx, %rax⸩

theorem swap_correct [layout : Host swap] (d : MachineData) :
    (layout swap).Spec d
      (post := fun st =>
        st.data.regs.get Reg.rax = d.regs.get Reg.rbx ∧
        st.data.regs.get Reg.rbx = d.regs.get Reg.rax) := by
  kprologue swap with d
  kfinish swap

def p2 : Program := ⸨prog|
start:
  mov $1, %rax
  xor %rax, %rax
  jnz start
  mov $2, %rax⸩

example [layout : Host p2] (s : MachineData) :
    (layout p2).Spec s (post := fun st => st.data.regs.rax = 2) := by
  kprologue p2 with s
  kfinish p2

def p4 := eval% ⸨prog|start: mov $2, %rax
dec %rax⸩

example [layout : Host p4] (s : MachineData) :
    (layout p4).Spec s (post := fun st => st.data.regs.rax = 1) := by
  kprologue p4 with s
  kfinish p4

def p5 := ⸨prog|start: mov $2, %rax
dec %rax
start2:
dec %rax⸩

example [layout : Host p5] (s : MachineData) :
    (layout p5).Spec s (post := fun st => st.data.regs.rax = 0) := by
  kprologue p5 with s
  kfinish p5

/-! ### Stack and Memory Addressing Examples -/

def p6 := ⸨prog|push %rax
mov $0, %rax
pop %rax⸩

theorem p6_correct [layout : Host p6] (s₀ : MachineData)
    (stack : List UInt8) (R : DataMem → Prop) :
    (layout p6).Spec s₀
      (pre :=
        stack.length = 8 ∧
        (s₀.dmem =⋆ stack @ s₀.regs.rsp - 8 ⋆ R))
      (post := fun st =>
        st.data.regs.rax = s₀.regs.rax ∧ st.data.regs.rsp = s₀.regs.rsp) := by
  kprologue p6 with s₀
  kstep
  apply Eventually.done
  simp (config := { zetaDelta := true }) only [show (OfNat.ofNat 8 : UInt64) = 8 from rfl]
  grind

-- A data word whose value is a label difference. `jmp done` keeps execution off the word.
def p7 : Program := ⸨prog|
start:
  nop 5
  nop 3
end:
  movl size(%rip), %eax
  jmp done
size:
  .long end - start
done:
⸩

/--
`p7` loads the word at `size`, whose value is the label difference `end - start`, kept symbolic.
The hypothesis `h_mem` says the loader put that value in memory: nothing in this framework links
the program text to memory yet, so it is assumed.
-/
theorem p7_correct [layout : Host p7] (s₀ : MachineData) (R : DataMem → Prop) :
    (layout p7).Spec s₀
      (pre :=
        letI := (layout p7).labels
        s₀.dmem =⋆ Eq ((Int.toBytes 4 (label "end" - label "start").toInt).At (label "size").toBitVec) ⋆ R)
      (post := fun st =>
        letI := (layout p7).labels
        st.data.regs.rax = UInt64.ofBitVec (((label "end" - label "start").toBitVec.setWidth 32).setWidth 64)) := by
  intro h_mem
  have h_val (v : BitVec 64) :
      BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 v.toInt)) = v.setWidth 32 := by
    rw [ofBytes_toBytes, Int.take, show 8 * 4 = 32 from rfl,
      ← BitVec.signExtend_eq_setWidth_of_le _ (by decide)]
    simp [BitVec.ofInt, BitVec.signExtend]
  kprologue p7 to "size" with s₀
  kstep
  kprologue p7 at "done"
  kstep
  apply Eventually.done
  simp only [h_val]

-- The same run under `fakeLayout`, where the nops take 5 + 3 bytes. The eval plays the loader: it
-- stores the word's value at `size`.
/-- info: Except.ok 8 -/
#guard_msgs in
#eval
  let exe := p7.fakeLayout
  let := exe.labels
  let word : Int64 := label "end" - label "start"
  let data : MachineData := { dmem := Mem.storeInt {} (label "size").toBitVec 4 word.toInt }
  (exe.eval {data, pc := label "start"} (fun st => st.pc = label "done")).bind
    (fun s => .ok s.1.regs.rax)

def move_2_regs_to_heap := ⸨prog|
    movq %rax, (%rdi)
    movq %rcx, 8(%rdi)
    movq (%rdi), %r12
    movq 8(%rdi), %r13
⸩

theorem move_2_regs_to_heap_correct [layout : Host move_2_regs_to_heap] (s₀ : MachineData)
    (v1 v2 : UInt64) (R : DataMem → Prop) :
    (layout move_2_regs_to_heap).Spec s₀
      (pre :=
        s₀.dmem =⋆ v1 @ s₀.regs.rdi ⋆ v2 @ s₀.regs.rdi + 8 ⋆ R)
      (post := fun st =>
        st.data.regs.r12 = s₀.regs.rax ∧
        st.data.regs.r13 = s₀.regs.rcx ∧
        st.data.regs.rdi = s₀.regs.rdi) := by
  kprologue move_2_regs_to_heap with s₀
  kfinish move_2_regs_to_heap

def sib_example := ⸨prog|
    movq $42, %rax
    movq %rax, (%rdi, %r15, 8)
    movq $0, %rax
    movq (%rdi, %r15, 8), %rax⸩

theorem sib_example_correct [layout : Host sib_example] (s₀ : MachineData)
    (v : UInt64) (R : DataMem → Prop) :
    (layout sib_example).Spec s₀
      (pre :=
        s₀.dmem =⋆ v @ s₀.regs.rdi + s₀.regs.r15 * 8 ⋆ R)
      (post := fun st => st.data.regs.rax = 42) := by
  kprologue sib_example with s₀
  kfinish sib_example

def alu_mem_example := ⸨prog|
    movq $42, %rax
    movq %rax, 136(%rdx)
    movq $100, %rcx
    addq 136(%rdx), %rcx⸩

theorem alu_mem_example_correct [layout : Host alu_mem_example] (s₀ : MachineData)
    (v : UInt64) (R : DataMem → Prop) :
    (layout alu_mem_example).Spec s₀
      (pre :=
        s₀.dmem =⋆ v @ s₀.regs.rdx + 136 ⋆ R)
      (post := fun st => st.data.regs.rcx = 142) := by
  kprologue alu_mem_example with s₀
  kfinish alu_mem_example

def dynamic_stack_example := ⸨prog|
    movq $99, -8(%rsp)
    movq %rsp, %rbp
    leaq -1024(%rsp, %r9, 8), %rsp
    movq $42, %rax
    movq %rax, 16(%rsp, %r15, 8)
    movq $0, %rax
    movq 16(%rsp, %r15, 8), %rax
    movq %rbp, %rsp
    movq -8(%rsp), %rbx⸩

theorem dynamic_stack_example_correct [layout : Host dynamic_stack_example] (s₀ : MachineData)
    (stack : List UInt8) (R : DataMem → Prop) :
    (layout dynamic_stack_example).Spec s₀
      (pre :=
        stack.length = 1024 ∧
        s₀.regs.r9.toNat + s₀.regs.r15.toNat < 125 ∧
        (s₀.dmem =⋆ stack @ s₀.regs.rsp - 1024 ⋆ R))
      (post := fun st =>
        st.data.regs.rax = 42 ∧ st.data.regs.rbx = 99 ∧ st.data.regs.rsp = s₀.regs.rsp) := by
  rintro ⟨lstack, h, h_mem⟩
  kprologue dynamic_stack_example with s₀
  rw [Mem.At_take_drop_sep stack 1016 _ (by omega) (by omega)] at h_mem
  rw [Mem.At_slice_sep (stack.take 1016) ((r9.toNat + r15.toNat) * 8 + 16) 8 _
    (by simp [lstack]; omega) (by simp [lstack])] at h_mem
  kfinish dynamic_stack_example

/-! ### Loops -/

def p3 : Program := ⸨prog|
init:
  mov $2, %rdx             -- rdx: current result = 2
start:
  sub $0, %rbx             -- TEST: zf = (rbx == 0)
  jz _end                  -- end loop if rbx == 0
  mulx %rdx, %rdx, %rax    -- BODY: rdx := rdx * rdx
  sub $1, %rbx             -- rbx -= 1
  jmp start                -- repeat loop
_end:
  nop
⸩

def p3_spec (s : MachineData) : Nat := 2 ^ (2 ^ s.regs.rbx.toNat)

theorem p3_correct [layout : Host p3] (s : MachineData) :
    (layout p3).Spec s
      (pre := p3_spec s < 2 ^ 64)
      (post := fun st =>
        st.data.regs.rdx.toNat = p3_spec s ∧ (0 < s.regs.rbx.toNat → st.data.regs.rax = 0)) := by
  intro h_bounds
  unfold p3_spec at *
  kprologue p3 to "start"
  kstep
  kloop at "start"
    (inv := fun i st =>
      st.data.regs.rbx.toNat = i ∧
      i ≤ s.regs.rbx.toNat ∧
      st.data.regs.rdx.toNat = 2 ^ (2 ^ (s.regs.rbx.toNat - i)) ∧
      (i < s.regs.rbx.toNat → st.data.regs.rax = 0))
    (measure := s.regs.rbx.toNat)
    (state := state)
    with k _ ⟨h_rbx_k, h_k_le, h_inv, h_rax⟩
  · exact ⟨rfl, Nat.le_refl _, by simp; decide, fun h => absurd h (Nat.lt_irrefl _)⟩
  · by_cases hk : k = 0
    · subst hk
      kprologue p3 at "start" with state
      kstep
      kprologue p3 at "_end"
      kloop_exit
      exact ⟨by rw [h_inv, Nat.sub_zero], fun h_pos => h_rax h_pos⟩
    · kprologue p3 at "start" to "_end" with state
      kstep
      rename_i _ b_mul v_mul _ _ _
      have h_pow_eq : rdx.toNat * rdx.toNat = 2 ^ 2 ^ (s.regs.rbx.toNat - (k - 1)) := by
        rw [h_inv, show s.regs.rbx.toNat - (k - 1) = (s.regs.rbx.toNat - k) + 1 by omega]
        rw [← Nat.pow_two, ← Nat.pow_mul, ← Nat.pow_succ]
      have h_prod_lt : rdx.toNat * rdx.toNat < 2 ^ 64 := by
        rw [h_pow_eq]
        refine Nat.lt_of_le_of_lt ?_ h_bounds
        apply Nat.pow_le_pow_right (by decide)
        apply Nat.pow_le_pow_right (by decide)
        omega
      have hv_mul : v_mul = ↑(rdx.toNat * rdx.toNat) := by
        dsimp [v_mul, b_mul, BitVec.unsigned] <;> grind
      kloop_next (k - 1)
      refine ⟨by grind, by omega, ?_, ?_⟩
      · rw [hv_mul, ← h_pow_eq]
        change (BitVec.ofNat 64 (rdx.toNat * rdx.toNat)).toNat = rdx.toNat * rdx.toNat
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_prod_lt]
      · intro _
        rw [hv_mul]
        change ({ toBitVec := BitVec.ofNat 64 ((rdx.toNat * rdx.toNat) >>> 64) } : UInt64) = 0
        have h_shr : (rdx.toNat * rdx.toNat) >>> 64 = 0 :=
          Nat.shiftRight_eq_div_pow _ _ ▸ Nat.div_eq_of_lt h_prod_lt
        rw [h_shr]
        rfl

/-- Loop zeroing an array of `n` 64-bit words in memory. -/
def memset_loop : Program := ⸨prog|
loop:
  movq $0, (%rdi)
  addq $8, %rdi
  subq $1, %rcx
  jnz loop
⸩

theorem memset_loop_correct [layout : Host memset_loop] (s₀ : MachineData)
    (n : Nat) (buf : List UInt8) (R : DataMem → Prop) :
    (layout memset_loop).Spec s₀
      (pre :=
        0 < n ∧
        s₀.regs.rcx.toNat = n ∧
        buf.length = 8 * n ∧
        buf.length ≤ 2 ^ 64 ∧
        (s₀.dmem =⋆ buf @ s₀.regs.rdi ⋆ R))
      (post := fun st =>
        st.data.regs.rcx = 0 ∧
        st.data.regs.rdi.toBitVec = s₀.regs.rdi.toBitVec + BitVec.ofNat 64 (8 * n) ∧
        (st.data.dmem =⋆ (List.replicate (8 * n) 0) @ s₀.regs.rdi ⋆ R)) := by
  rintro ⟨hn, h_rcx, h_len, h_bound, h_mem⟩
  kloop
    (pc := layout.start)
    (inv := fun v (ptr, bs, frame) st =>
      0 < v ∧
      st.data.regs.rcx.toNat = v ∧
      st.data.regs.rdi.toBitVec = ptr ∧
      bs.length = 8 * v ∧
      bs.length ≤ 2 ^ 64 ∧
      (st.data.dmem =⋆ bs @ ptr ⋆ frame))
    (exit := fun v (ptr, _, frame) st =>
      st.data.regs.rcx = 0 ∧
      st.data.regs.rdi.toBitVec = ptr + BitVec.ofNat 64 (8 * v) ∧
      (st.data.dmem =⋆ (List.replicate (8 * v) 0) @ ptr ⋆ frame))
    (measure := n)
    (ghost := (s₀.regs.rdi.toBitVec, buf, R))
    (state := s)
    with v ⟨ptr, bs, frame⟩ ⟨hv, h_rcx, rfl, h_bs_len, h_bs_bound, h_mem⟩
  · kloop_next
    exact ⟨hn, h_rcx, rfl, h_len, h_bound, h_mem⟩
  · by_cases hv1 : v = 1
    · subst hv1
      kprologue memset_loop with s
      kloop_exit
      kfinish memset_loop
    · kprologue memset_loop with s
      rw [Mem.At_take_drop_sep bs 8 rdi.toBitVec (by omega) h_bs_bound] at h_mem
      kloop_next (v - 1) (rdi.toBitVec + 8#64, bs.drop 8, (List.replicate 8 0) @ rdi ⋆ frame)
      · exact ⟨by grind, by grind, by grind, by simp [h_bs_len]; omega, by simp; omega, by ecancel⟩
      rintro t_s ⟨hQ_rcx, hQ_rdi, hQ_mem⟩
      refine ⟨hQ_rcx, by grind, ?_⟩
      rw [Mem.At_take_drop_sep _ 8 _ (by simp; omega) (by simp; omega)]
      ecancel
  · exact Eventually.done _ hs

/-! ### Composable Block Specifications -/

/-- Standalone basic block that swaps two 64-bit words in memory at `(%rdi)` and `(%rsi)`. -/
def swap_mem_block : Program := ⸨prog|
  movq (%rdi), %rax
  movq (%rsi), %rcx
  movq %rcx, (%rdi)
  movq %rax, (%rsi)
⸩

/-- Verified once for any `[layout : Layout]` and `[Labels]` using `Executable.ExecSpec`. -/
theorem swap_mem_block_spec [layout : Layout] [Labels] (s₀ : MachineData)
    (x y : UInt64) (R : DataMem → Prop) :
    (layout swap_mem_block).ExecSpec s₀
      (pre :=
        s₀.dmem =⋆ x @ s₀.regs.rdi ⋆ y @ s₀.regs.rsi ⋆ R)
      (post := fun st =>
        st.pc = (layout swap_mem_block).addrOf swap_mem_block.length ∧
        st.data.regs.rax = x.toBitVec ∧
        st.data.regs.rcx = y.toBitVec ∧
        st.data.regs.rdi = s₀.regs.rdi ∧
        st.data.regs.rsi = s₀.regs.rsi ∧
        (st.data.dmem =⋆ y @ s₀.regs.rdi ⋆ x @ s₀.regs.rsi ⋆ R)) := by
  kprologue swap_mem_block with s₀
  kfinish swap_mem_block

/-- Program embedding `swap_mem_block` followed by a `finish:` block. -/
def swap_and_add : Program := ⸨prog|
  movq (%rdi), %rax
  movq (%rsi), %rcx
  movq %rcx, (%rdi)
  movq %rax, (%rsi)
finish:
  addq %rcx, %rax
⸩

/-- Basic-block lemma for the `finish:` block within `swap_and_add`. -/
block_spec swap_and_add_finish_spec swap_and_add s
  from "finish"
  (post := fun st =>
    st.data.regs.rax = s.regs.rax + s.regs.rcx ∧
    st.data.dmem = s.dmem) := by
  kprologue swap_and_add at "finish" with s
  kfinish swap_and_add

/-- Composing `swap_mem_block_spec` (`step1_subprog`) with `swap_and_add_finish_spec` (`kcall`). -/
block_spec swap_and_add_correct swap_and_add s₀ (x y : UInt64) (R : DataMem → Prop)
  (pre :=
    s₀.dmem =⋆ x @ s₀.regs.rdi ⋆ y @ s₀.regs.rsi ⋆ R)
  (post := fun st =>
    st.data.regs.rax = x.toBitVec + y.toBitVec ∧
    (st.data.dmem =⋆ y @ s₀.regs.rdi ⋆ x @ s₀.regs.rsi ⋆ R)) := by
  intro h_mem
  refine step1_subprog 0 (swap_mem_block_spec s₀ x y R) h_mem (by rfl) (by kaddr swap_and_add) ?_
  rintro s₁ ⟨h_rax, h_rcx, -, -, h_mem₁⟩
  kcall swap_and_add_finish_spec s₁ with s₂ ⟨h_rax₂, h_dmem₂⟩
  apply Eventually.done
  exact ⟨by grind, h_dmem₂ ▸ h_mem₁⟩

/-- Constant-time specification for `swap_mem_block` using `ExecSpec (trace := some tr)`. -/
theorem swap_mem_block_ct_spec [layout : Layout] [Labels] (x_ptr y_ptr : BitVec 64) :
    ∃ tr, ∀ (s₀ : MachineData) (x y : UInt64) (R : DataMem → Prop),
      (layout swap_mem_block).ExecSpec s₀
        (trace := some tr)
        (pre :=
          s₀.regs.rdi = x_ptr ∧ s₀.regs.rsi = y_ptr ∧
          (s₀.dmem =⋆ x @ x_ptr ⋆ y @ y_ptr ⋆ R))
        (post := fun st =>
          st.pc = (layout swap_mem_block).addrOf swap_mem_block.length ∧
          st.data.regs.rax = x.toBitVec ∧
          st.data.regs.rcx = y.toBitVec ∧
          st.data.regs.rdi = x_ptr ∧
          st.data.regs.rsi = y_ptr ∧
          (st.data.dmem =⋆ y @ x_ptr ⋆ x @ y_ptr ⋆ R)) := by
  kprologue swap_mem_block with s₀
  kfinish swap_mem_block

/-- Constant-time specification for the `finish:` block within `swap_and_add`. -/
block_spec swap_and_add_finish_ct_spec swap_and_add s
  from "finish" ct
  (post := fun st =>
    st.data.regs.rax = s.regs.rax + s.regs.rcx ∧
    st.data.dmem = s.dmem) := by
  kprologue swap_and_add at "finish" with s
  kfinish swap_and_add

/-- Composing `swap_mem_block_ct_spec` (`step1_subprog_traced`) with `swap_and_add_finish_ct_spec`. -/
block_spec swap_and_add_ct_correct swap_and_add (x_ptr y_ptr : BitVec 64)
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

/-! ### Function Pointers and Jump Tables -/

/-- Materializing a subroutine's address with `%rip`-relative `leaq`, calling it indirectly with
`callq %rcx`, and returning with `retq`. -/
def fn_ptr_call : Program := ⸨prog|
  leaq add_ten(%rip), %rcx
  callq %rcx
  jmp done
add_ten:
  addq $10, %rax
  retq
done:
  nop
⸩

theorem fn_ptr_call_correct [layout : Host fn_ptr_call] (s₀ : MachineData)
    (ret_slot : UInt64) (R : DataMem → Prop) :
    (layout fn_ptr_call).Spec s₀
      (pre := s₀.dmem =⋆ ret_slot @ (s₀.regs.rsp - 8) ⋆ R)
      (post := fun st =>
        st.data.regs.rax = s₀.regs.rax + 10 ∧
        st.data.regs.rsp = s₀.regs.rsp) := by
  intro h_mem
  kprologue fn_ptr_call to "add_ten" with s₀
  kstep
  kprologue fn_ptr_call at "add_ten"
  kstep
  kprologue fn_ptr_call at 2
  kfinish fn_ptr_call

/-- Higher-order caller that invokes a callback at `fn_ptr` via `callq %rcx` and increments its return value. -/
def apply_callback : Program := ⸨prog|
  callq %rcx
  addq $1, %rax
⸩

theorem apply_callback_correct [layout : Host apply_callback] (s₀ : MachineData)
    (fn_ptr : Int64) (f : UInt64 → UInt64) (ret_slot : UInt64) (R : DataMem → Prop)
    (h_cb : ∀ (s : MachineData) (ra : UInt64),
      (layout apply_callback).Spec s
        (pc := fn_ptr)
        (pre := s.dmem =⋆ ra @ s.regs.rsp ⋆ R)
        (post := fun st =>
          st.pc = Int64.ofBitVec ra.toBitVec ∧
          st.data.regs.rax = f s.regs.rax ∧
          st.data.regs.rsp = s.regs.rsp + 8 ∧
          (st.data.dmem =⋆ ra @ s.regs.rsp ⋆ R))) :
    (layout apply_callback).Spec s₀
      (pre :=
        Int64.ofBitVec s₀.regs.rcx.toBitVec = fn_ptr ∧
        (s₀.dmem =⋆ ret_slot @ (s₀.regs.rsp - 8) ⋆ R))
      (post := fun st =>
        st.data.regs.rax = f s₀.regs.rax + 1 ∧
        st.data.regs.rsp = s₀.regs.rsp) := by
  rintro ⟨h_fn, h_mem⟩
  kprologue apply_callback take 1 with s₀
  kstep
  rw [h_fn]
  kcall h_cb _ (UInt64.ofBitVec ((layout apply_callback).addrOf 0 + Int64.ofNat (layout.size 0)).toBitVec)
    with s₁ ⟨h_rax, h_rsp, h_mem₁⟩
  kprologue apply_callback at 1
  kfinish apply_callback

/-- 3-way jump-table dispatch (`%rip`-relative `leaq` + SIB indirect `jmp (%rcx, %rdi, 8)`). -/
def jump_table : Program := ⸨prog|
  leaq .Ltable(%rip), %rcx
  jmp (%rcx, %rdi, 8)
.Lcase0:
  movq $10, %rax
  jmp .Ldone
.Lcase1:
  movq $20, %rax
  jmp .Ldone
.Lcase2:
  movq $30, %rax
  jmp .Ldone
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
        s₀.regs.rdi.toNat < 3 ∧
        (s₀.dmem =⋆ c0 @ tbl ⋆ c1 @ (tbl + 8#64) ⋆ c2 @ (tbl + 16#64) ⋆ R))
      (post := fun st =>
        st.data.regs.rax = match s₀.regs.rdi.toNat with | 0 => 10 | 1 => 20 | _ => 30) := by
  rintro ⟨h_idx, h_mem⟩
  have h_cases : s₀.regs.rdi = 0 ∨ s₀.regs.rdi = 1 ∨ s₀.regs.rdi = 2 := by
    rcases (show s₀.regs.rdi.toNat = 0 ∨ s₀.regs.rdi.toNat = 1 ∨ s₀.regs.rdi.toNat = 2 by omega) with h | h | h
    · left; exact UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (by simp [h]))
    · right; left; exact UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (by simp [h]))
    · right; right; exact UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (by simp [h]))
  rcases h_cases with h0 | h1 | h2
  · kprologue jump_table to ".Lcase0" with s₀
    subst h0
    kstep
    kprologue jump_table at ".Lcase0"
    kfinish jump_table
  · kprologue jump_table to ".Lcase0" with s₀
    subst h1
    kstep
    kprologue jump_table at ".Lcase1"
    kfinish jump_table
  · kprologue jump_table to ".Lcase0" with s₀
    subst h2
    kstep
    kprologue jump_table at ".Lcase2"
    kfinish jump_table


