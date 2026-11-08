module

import Kraken.X64.OmniSemantics
import Kraken.X64.Parser
import Kraken

macro (priority := low) "kprologue " x:term " with " s:ident : tactic =>
  `(tactic| (generalize $x = prog; kprologue prog with $s))

attribute [grind hom] UInt64.ofBitVec_xor


/-- Swaps `rax` and `rbx`-/
def swap := ⸨prog|
swap: xor %rax, %rbx
      xor %rbx, %rax
      xor %rax, %rbx
      jmp %rcx
⸩


theorem swap.sem [l : Layout]
  (st : MachineData) :
    letI e : Executable := l.apply swap
    letI : Labels := e.labels
    Eventually (straightlineStep e)
      (post := fun ⟨st', pc⟩ =>
        ∃ status,
        st' = {st with
          regs := {st.regs with
            rax := st.regs.rbx
            rbx := st.regs.rax
          }
          status
        } ∧
        pc.toUInt64 = st.regs.rcx
      )
      ⟨st, l.start⟩ := by
  apply step_cps
  kprologue swap with st
  dsimp +zetaDelta only [
    Directives.interp, Directive.interp, Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, Reg.interp, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.set, Reg64s.get64, Reg64s.set64, Reg.base, Reg.offset,
    BitVec.take, BitVec.drop, StatusFlags.from_result, Width.bits, Width.type, Effects.All
  ]
  intros
  simp only [Nat.sub_zero]
  apply Eventually.done
  simp [Reg64s.get, Reg.offset, Reg.base, BitVec.take, Reg64s.get64, BitVec.drop]

  -- rename StatusFlags => st; clear st
  -- rename BitVec 64 => v₃; unfold v₃; simp; clear v₃
  -- rename StatusFlags => st; clear st
  -- rename BitVec 64 => v₂; unfold v₂; simp; clear v₂
  -- rename StatusFlags => st; clear st
  -- rename BitVec 64 => v₄; unfold v₄; simp; clear v₄

  grind [UInt64.xor_comm, UInt64.xor_assoc, UInt64.ofBitVec_xor]

def Layout.programSize [l : Layout] (p : Program) : Nat := List.range p.length |>.map l.size |>.sum

set_option warn.classDefReducibility false in
def Layout.after [l : Layout] (p : Program) : Layout := {start := l.start + Int64.ofNat (l.programSize p), size i := l.size (p.length + i)}
def Layout.applyAfter [l : Layout] (p p₂ : Program) : Executable := (l.after p).apply p₂

def foo (l : Layout /-p₁ ++ p₂ ++ p₃-/) (p₁ p₂ p₃ : Program)
  (post : MachineState → Prop) (init : MachineState)
  (h : ∀ (l₂ : Layout), Eventually (step1 (l₂.apply p₂)) post init) :
    Eventually (step1 (l.apply (p₁ ++ p₂ ++ p₃))) post init := by
  let l₂ : Layout := l.after p₁
  sorry

abbrev straightlineStepExit (init st : MachineState) : Prop := True

theorem straightlineStep_step1 [l : Layout] (p : Program) (init : MachineState) (post : MachineState → Prop) :
    straightlineStep (l.apply p) init post ↔
    Eventually (step1 (l.apply p)) (fun st => straightlineStepExit init st ∧ post st) init := by
  sorry

open Std.WP in
#check WP.Frames

def client := ⸨prog|
  La: mov $41, %rax
      mov $42, %rbx
      mov Lb,  %rcx

      jmp swap

  Lb: test %rax, %rbx
⸩

instance : Append Executable where
  append a b := {a with program := a.program ++ b.program}


theorem Executable.split [l : Layout] (p₁ p₂ : Program) : l.apply (p₁ ++ p₂) = l.apply p₁ ++ (l.after p₁).apply p₂ := by
  sorry

theorem Eventually.cons [l : Layout] (p₁ p₂ : Program) (post mid_p : MachineState → Prop) (init : MachineState) :
    Eventually (straightlineStep (l.apply p₁)) mid_p init →
    (∀ s, mid_p s → Eventually (step1 (l.applyAfter p₁ p₂)) mid_p init)  →
    Eventually (straightlineStep (l.apply (p₁ ++ p₂))) post init := by
  sorry

-- NOTE: How do we state a spec for `client` without `swap`?
theorem client.sem [l : Layout]
  (st : MachineData) :
    letI e : Executable := l.apply (client ++ swap)
    Eventually (straightlineStep e)
      (post := fun _ => True)
      ⟨st, l.start⟩ := by
  apply step_cps
  let {dmem := mem, regs := ⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, status} := st
  unfold client swap; simp only [List.cons_append, List.nil_append]
  dsimp [straightlineStep, Executable.straightline]
  rw [Kraken.Executable.directivesFromStart]
  simp [List.mapIdx, List.mapIdx.go]
  sym => kstep 1; tactic =>
  sym => kstep 1; tactic =>
  sym => kstep 1; tactic =>
  sym => kstep 1; tactic =>
  skip

  dsimp only [$straightlineStepId:ident, $execStraightlineId:ident]
  rw [Executable.directivesFromStart]
  simp [List.mapIdx, List.mapIdx.go])))

  kprologue total with st
  sym => kstep; tactic =>
