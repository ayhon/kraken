module

import Kraken.Attribute
public import Kraken.Layout
public import Lean.ToExpr
meta import Lean.Elab.Deriving.ToExpr

/-!
# x86-64 Assembly Syntax

Registers, widths, constant and address expressions, operands, condition codes,
instructions, and directives for x86-64.
-/

@[expose] public section

/-! ### Widths and Registers -/

inductive AvxWidth | W128 | W256 | W512
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

instance : ToString AvxWidth where
  toString | .W128 => "w128" | .W256 => "w256" | .W512 => "w512"

namespace AvxWidth
@[simp, reducible] def bits : AvxWidth → Nat | W128 => 128 | W256 => 256 | W512 => 512
@[simp, reducible] def bytes : AvxWidth → Nat | W128 => 16 | W256 => 32 | W512 => 64
abbrev bytesv (w : AvxWidth) {n} : BitVec n := BitVec.ofNat n w.bytes
abbrev type (w : AvxWidth) : Type := BitVec w.bits
instance {w : AvxWidth} : Coe Bool w.type where coe := fun b : Bool => BitVec.ofNat _ b.toNat
end AvxWidth

unif_hint (w : AvxWidth) where
  w =?= AvxWidth.W128 |- AvxWidth.type w =?= BitVec 128

unif_hint (w : AvxWidth) where
  w =?= AvxWidth.W256 |- AvxWidth.type w =?= BitVec 256

unif_hint (w : AvxWidth) where
  w =?= AvxWidth.W512 |- AvxWidth.type w =?= BitVec 512

inductive RegMm
  | mm0  | mm1  | mm2  | mm3
  | mm4  | mm5  | mm6  | mm7
  | mm8  | mm9  | mm10 | mm11
  | mm12 | mm13 | mm14 | mm15
  | mm16 | mm17 | mm18 | mm19
  | mm20 | mm21 | mm22 | mm23
  | mm24 | mm25 | mm26 | mm27
  | mm28 | mm29 | mm30 | mm31
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

inductive Reg64
  | rax | rbx | rcx | rdx
  | rsi | rdi | rsp | rbp
  | r8  | r9  | r10 | r11
  | r12 | r13 | r14 | r15
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

inductive Reg : Width → Type
  | low (_ : Reg64) (w : Width) : Reg w
  | ah : Reg .W8 | bh : Reg .W8 | ch : Reg .W8 | dh : Reg .W8
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

inductive AvxReg : AvxWidth → Type
  | xmm (_ : RegMm) : AvxReg AvxWidth.W128
  | ymm (_ : RegMm) : AvxReg AvxWidth.W256
  | zmm (_ : RegMm) : AvxReg AvxWidth.W512
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

structure RegW where
  w : Width
  reg : Reg w
  deriving Repr, DecidableEq, Hashable, Lean.ToExpr

structure AvxRegW where
  w : AvxWidth
  reg : AvxReg w
  deriving Repr, DecidableEq, Hashable, Lean.ToExpr

namespace Reg
@[match_pattern] abbrev rax := low .rax .W64
@[match_pattern] abbrev rbx := low .rbx .W64
@[match_pattern] abbrev rcx := low .rcx .W64
@[match_pattern] abbrev rdx := low .rdx .W64
@[match_pattern] abbrev rsi := low .rsi .W64
@[match_pattern] abbrev rdi := low .rdi .W64
@[match_pattern] abbrev rsp := low .rsp .W64
@[match_pattern] abbrev rbp := low .rbp .W64
@[match_pattern] abbrev r8  := low .r8  .W64
@[match_pattern] abbrev r9  := low .r9  .W64
@[match_pattern] abbrev r10 := low .r10 .W64
@[match_pattern] abbrev r11 := low .r11 .W64
@[match_pattern] abbrev r12 := low .r12 .W64
@[match_pattern] abbrev r13 := low .r13 .W64
@[match_pattern] abbrev r14 := low .r14 .W64
@[match_pattern] abbrev r15 := low .r15 .W64

@[match_pattern] abbrev eax  := low .rax .W32
@[match_pattern] abbrev ebx  := low .rbx .W32
@[match_pattern] abbrev ecx  := low .rcx .W32
@[match_pattern] abbrev edx  := low .rdx .W32
@[match_pattern] abbrev esi  := low .rsi .W32
@[match_pattern] abbrev edi  := low .rdi .W32
@[match_pattern] abbrev esp  := low .rsp .W32
@[match_pattern] abbrev ebp  := low .rbp .W32
@[match_pattern] abbrev r8d  := low .r8  .W32
@[match_pattern] abbrev r9d  := low .r9  .W32
@[match_pattern] abbrev r10d := low .r10 .W32
@[match_pattern] abbrev r11d := low .r11 .W32
@[match_pattern] abbrev r12d := low .r12 .W32
@[match_pattern] abbrev r13d := low .r13 .W32
@[match_pattern] abbrev r14d := low .r14 .W32
@[match_pattern] abbrev r15d := low .r15 .W32

@[match_pattern] abbrev ax   := low .rax .W16
@[match_pattern] abbrev bx   := low .rbx .W16
@[match_pattern] abbrev cx   := low .rcx .W16
@[match_pattern] abbrev dx   := low .rdx .W16
@[match_pattern] abbrev si   := low .rsi .W16
@[match_pattern] abbrev di   := low .rdi .W16
@[match_pattern] abbrev sp   := low .rsp .W16
@[match_pattern] abbrev bp   := low .rbp .W16
@[match_pattern] abbrev r8w  := low .r8  .W16
@[match_pattern] abbrev r9w  := low .r9  .W16
@[match_pattern] abbrev r10w := low .r10 .W16
@[match_pattern] abbrev r11w := low .r11 .W16
@[match_pattern] abbrev r12w := low .r12 .W16
@[match_pattern] abbrev r13w := low .r13 .W16
@[match_pattern] abbrev r14w := low .r14 .W16
@[match_pattern] abbrev r15w := low .r15 .W16

@[match_pattern] abbrev al   := low .rax .W8
@[match_pattern] abbrev bl   := low .rbx .W8
@[match_pattern] abbrev cl   := low .rcx .W8
@[match_pattern] abbrev dl   := low .rdx .W8
@[match_pattern] abbrev sil  := low .rsi .W8
@[match_pattern] abbrev dil  := low .rdi .W8
@[match_pattern] abbrev spl  := low .rsp .W8
@[match_pattern] abbrev bpl  := low .rbp .W8
@[match_pattern] abbrev r8b  := low .r8  .W8
@[match_pattern] abbrev r9b  := low .r9  .W8
@[match_pattern] abbrev r10b := low .r10 .W8
@[match_pattern] abbrev r11b := low .r11 .W8
@[match_pattern] abbrev r12b := low .r12 .W8
@[match_pattern] abbrev r13b := low .r13 .W8
@[match_pattern] abbrev r14b := low .r14 .W8
@[match_pattern] abbrev r15b := low .r15 .W8
end Reg

/-! ### Constant and Address Expressions -/

/-- Assembler constant expression, evaluated using 64-bit arithmetic. -/
inductive ConstExpr
  | label (_ : Label)
  | int64 (_ : Int64)
  | before_current_instruction | after_current_instruction
  | add (_ _ : ConstExpr) | sub (_ _ : ConstExpr)
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

instance : Coe Label ConstExpr where coe := .label
instance : Coe Int64 ConstExpr where coe := .int64
instance {n} [OfNat Int64 n] : OfNat ConstExpr n where ofNat := .int64 (OfNat.ofNat n)
attribute [coe] ConstExpr.label
attribute [coe] ConstExpr.int64

/-- Base register or `%rip` in an address expression. High-byte registers (`%ah`–`%dh`) cannot
appear in memory operands, and the effective address width is determined by the instruction-wide
`AddressSize` prefix rather than per-register width annotations. -/
inductive RegOrRip where
  | reg (_ : Reg64)
  | rip : RegOrRip
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

structure AddrIndex where
  reg : Reg64
  scale : Width
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

structure AddrExpr where
  base : Option RegOrRip
  idx : Option AddrIndex
  disp : ConstExpr := .int64 0
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

/-- Instruction-wide effective address width (e.g. `.W64`, or `.W32` under an `addr32` prefix). -/
class AddressSize where
  address_size : Width
export AddressSize (address_size)

/-! ### Operands and Condition Codes -/

inductive RegOrMem (w : Width)
  | reg (r : Reg w)
  | mem (_ : AddrExpr)
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

instance {w} : Coe AddrExpr (RegOrMem w) where coe := RegOrMem.mem
attribute [coe] RegOrMem.mem
instance {w} : Coe (Reg w) (RegOrMem w) where coe := .reg
attribute [coe] RegOrMem.reg
abbrev Dst := RegOrMem

inductive AvxRegOrMem (w : AvxWidth)
  | avx (r : AvxReg w)
  | mem (_ : AddrExpr)
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

instance {w} : Coe AddrExpr (AvxRegOrMem w) where coe := AvxRegOrMem.mem
attribute [coe] AvxRegOrMem.mem
instance {w} : Coe (AvxReg w) (AvxRegOrMem w) where coe := .avx
attribute [coe] AvxRegOrMem.avx
abbrev AvxDst := AvxRegOrMem

inductive Operand (w : Width)
  | regOrMem (_ : RegOrMem w)
  | imm (v : ConstExpr)
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

instance {w} : Coe (RegOrMem w) (Operand w) where coe := .regOrMem
attribute [coe] Operand.regOrMem
instance {w} : Coe ConstExpr (Operand w) where coe := Operand.imm
attribute [coe] Operand.imm
abbrev Operand.reg {w} (r : Reg w) : Operand w := regOrMem (.reg r)
abbrev Operand.mem {w} (m : AddrExpr) : Operand w := regOrMem (.mem m)

inductive AvxOperand (w : AvxWidth)
  | regOrMem (_ : AvxRegOrMem w)
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

instance {w} : Coe (AvxRegOrMem w) (AvxOperand w) where coe := .regOrMem
attribute [coe] AvxOperand.regOrMem
abbrev AvxOperand.avx {w} (r : AvxReg w) : AvxOperand w := regOrMem (.avx r)
abbrev AvxOperand.mem {w} (m : AddrExpr) : AvxOperand w := regOrMem (.mem m)

inductive CondCode | o | no | c | nc | z | nz | be | a | s | ns | p | np | l | ge | le | g
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr
abbrev CondCode.e := CondCode.z
abbrev CondCode.ne := CondCode.nz
abbrev CondCode.b := CondCode.c
abbrev CondCode.ae := CondCode.nc

inductive ShiftCountExpr | cl | imm8 (v : ConstExpr)
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

inductive RelRegOrMem | rel (_ : ConstExpr) | reg (r : Reg .W64) | mem (_ : AddrExpr)
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

/-! ### Operations, Instructions, and Directives -/

inductive Operation (w : Width)
  -- Data movement
  | mov (_ : Dst w) (src : Operand w)
  | movsx {w'} (_ : Dst w) (src : RegOrMem w')
  | movzx {w'} (_ : Dst w) (src : RegOrMem w')
  | push (src : Operand w)
  | pop  (_ : Dst w)
  | setcc (_ : CondCode) (_ : Dst w)
  | cmovcc (_ : CondCode) (_ : Reg w) (src : RegOrMem w)
  -- String moves and stores, once or with a `rep` prefix
  | movs (rep : Bool)
  | stos (rep : Bool)
  -- Arithmetic
  | lea (_ : Reg w) (src : AddrExpr)
  | add  (_ : Dst w) (src : Operand w)
  | adc  (_ : Dst w) (src : Operand w)
  | adcx (_ : Reg w) (src : RegOrMem w)
  | adox (dst : Reg w) (src : RegOrMem w)
  | inc  (_ : RegOrMem w)
  | dec  (_ : RegOrMem w)
  | neg  (_ : RegOrMem w)
  | sub  (_ : Dst w) (src : Operand w)
  | sbb  (_ : Dst w) (src : Operand w)
  | cmp  (a : RegOrMem w) (b : Operand w)
  | mul  (src : RegOrMem w)
  | mulx (hi lo : Reg w) (src : RegOrMem w)
  | imul1 (src : RegOrMem w)
  | imul (_ : Option (Dst w)) (src1 : RegOrMem w) (src2 : Operand w)
  -- Bitwise
  | test (a : RegOrMem w) (b : Operand w)
  | and  (_ : Dst w) (src : Operand w)
  | not  (_ : Dst w)
  | or   (_ : Dst w) (src : Operand w)
  | xor  (_ : Dst w) (src : Operand w)
  | shl  (_ : Dst w) (_ : ShiftCountExpr)
  | shr  (_ : Dst w) (_ : ShiftCountExpr)
  | sar  (_ : Dst w) (_ : ShiftCountExpr)
  | shld (_ : Dst w) (src : Reg w) (_ : ShiftCountExpr)
  | shrd (_ : Dst w) (src : Reg w) (_ : ShiftCountExpr)
  | rol  (_ : Dst w) (_ : ShiftCountExpr)
  | ror  (_ : Dst w) (_ : ShiftCountExpr)
  | rcl  (_ : Dst w) (_ : ShiftCountExpr)
  | rcr  (_ : Dst w) (_ : ShiftCountExpr)
  | bswap (dst : Reg w)
  -- Flag control
  | cld
  | std
  -- Control flow
  | jcc (cc : CondCode) (target : Label)
  | jmp (target : RelRegOrMem)
  | call (target : RelRegOrMem)
  | ret
  | nop (length : Nat)
  | nopalign (alignment : Nat) (pad : Option Nat)
  deriving Repr, DecidableEq, Hashable, Lean.ToExpr

/-- Vector / SSE operations (non-`v*` variants operate on legacy SSE registers). -/
inductive AvxOperation (w : AvxWidth)
  | movups (_ : AvxDst w) (src : AvxRegOrMem w)
  | vmovups (_ : AvxDst w) (src : AvxRegOrMem w)
  | movaps (_ : AvxDst w) (src : AvxRegOrMem w)
  | subps (_ : AvxDst w) (src : AvxRegOrMem w)
  | addps (_ : AvxDst w) (src : AvxRegOrMem w)
  -- SSE2, SSSE3, and SSE4.1 integer operations
  | movdqu (_ : AvxDst w) (src : AvxRegOrMem w)
  | movdqa (_ : AvxDst w) (src : AvxRegOrMem w)
  | paddd (_ : AvxDst w) (src : AvxRegOrMem w)
  | pshufb (_ : AvxDst w) (src : AvxRegOrMem w)
  | pshufd (_ : AvxDst w) (src : AvxRegOrMem w) (imm : ConstExpr)
  | palignr (_ : AvxDst w) (src : AvxRegOrMem w) (imm : ConstExpr)
  | pblendw (_ : AvxDst w) (src : AvxRegOrMem w) (imm : ConstExpr)
  -- VEX moves, which clear every bit above what they write
  | vmovdqu (_ : AvxDst w) (src : AvxRegOrMem w)
  -- `vmovd` when `n` is 32 bits, `vmovq` when it is 64
  | vmovIn (n : Width) (_ : AvxReg w) (src : RegOrMem n)
  | vmovOut (n : Width) (_ : Dst n) (src : AvxReg w)
  | vmovq (_ : AvxReg w) (src : AvxReg w)
  | vzeroupper
  -- SHA extensions
  | sha256rnds2 (_ : AvxDst w) (src : AvxRegOrMem w)  -- reads xmm0 implicitly
  | sha256msg1 (_ : AvxDst w) (src : AvxRegOrMem w)
  | sha256msg2 (_ : AvxDst w) (src : AvxRegOrMem w)
  -- AVX-512 integer operations, without write-masking
  | vmovdqu32 (_ : AvxDst w) (src : AvxRegOrMem w)
  | vmovdqa32 (_ : AvxDst w) (src : AvxRegOrMem w)
  | vpaddd (_ : AvxDst w) (src1 src2 : AvxRegOrMem w)
  | vprord (_ : AvxDst w) (src : AvxRegOrMem w) (imm : ConstExpr)
  | vpsrld (_ : AvxDst w) (src : AvxRegOrMem w) (imm : ConstExpr)
  | vpternlogd (_ : AvxDst w) (src2 src3 : AvxRegOrMem w) (imm : ConstExpr)
  deriving Repr, DecidableEq, Hashable, Lean.ToExpr

inductive Instr
  | regular (address_size : Width) (operation_size : Width) (operation : Operation operation_size)
  | avx (address_size : Width) (operation_size : AvxWidth) (operation : AvxOperation operation_size)
  deriving Repr, DecidableEq, Hashable, Lean.ToExpr

instance [AddressSize] {w : Width} : CoeOut (Operation w) Instr where
  coe op := Instr.regular address_size w op

instance [AddressSize] {w : AvxWidth} : CoeOut (AvxOperation w) Instr where
  coe op := Instr.avx address_size w op

abbrev Directive := Kraken.Directive Instr ConstExpr
abbrev Program := List Directive
abbrev Executable := Kraken.Executable Instr ConstExpr
