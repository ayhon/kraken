module

import Kraken.Attribute
public import Kraken.Layout
public import Lean.ToExpr
meta import Lean.Elab.Deriving.ToExpr

/-!
# AArch64 Assembly Syntax

Registers, widths, constant and address expressions, extensions, shifts,
condition codes, instructions, and directives for AArch64.
-/

@[expose] public section

/-! ### Widths and Registers -/

/-- Architectural operand and register width for AArch64 instructions:
- `W32`: 32-bit register (`W0`–`W30`, `WSP`, `WZR`) or 32-bit operation.
- `W64`: 64-bit register (`X0`–`X30`, `SP`, `XZR`) or 64-bit operation. -/
inductive RegWidth | W32 | W64
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

instance : ToString RegWidth where
  toString | .W32 => "w32" | .W64 => "w64"

namespace RegWidth
instance : Coe RegWidth Width where coe := fun w : RegWidth =>
  match w with
  | .W32 => .W32
  | .W64 => .W64
@[kstep, simp, reducible] def bits (w : RegWidth) : Nat := (w : Width).bits
@[kstep, simp, reducible] def bytes (w : RegWidth) : Nat := (w : Width).bytes
@[kstep] abbrev bytesv (w : RegWidth) {n} : BitVec n := (w : Width).bytesv
@[kstep] abbrev type (w : RegWidth) : Type := (w : Width).type
@[kstep, simp] instance {w : RegWidth} : Coe Bool w.type where coe := fun b : Bool => BitVec.ofNat _ b.toNat
end RegWidth

unif_hint (w : RegWidth) where
  w =?= RegWidth.W32 |- RegWidth.type w =?= BitVec 32

unif_hint (w : RegWidth) where
  w =?= RegWidth.W64 |- RegWidth.type w =?= BitVec 64

/-- AArch64 general-purpose registers `X0` through `X30`. -/
inductive XReg
  |  X0 |  X1 |  X2 |  X3 |  X4 |  X5 |  X6 |  X7
  |  X8 |  X9 | X10 | X11 | X12 | X13 | X14 | X15
  | X16 | X17 | X18 | X19 | X20 | X21 | X22 | X23
  | X24 | X25 | X26 | X27 | X28 | X29 | X30
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

/-- General-purpose register or stack pointer (`SP`/`WSP`), where register index 31 denotes SP. -/
inductive XRegOrSp
  | reg (_ : XReg)
  | SP
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

/-- General-purpose register or zero register (`XZR`/`WZR`), where register index 31 denotes ZR. -/
inductive XRegOrXzr
  | reg (_ : XReg)
  | XZR
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

inductive RegOrSp : RegWidth → Type
  | low (_ : XRegOrSp) (w : RegWidth) : RegOrSp w
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

inductive RegOrZr : RegWidth → Type
  | low (_ : XRegOrXzr) (w : RegWidth) : RegOrZr w
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

instance {w} : Coe XRegOrSp (RegOrSp w) where coe := fun r => .low r w
instance {w} : Coe XRegOrXzr (RegOrZr w) where coe := fun r => .low r w
instance {w} : Coe XReg (RegOrSp w) where coe := fun r => .low (.reg r) w
instance {w} : Coe XReg (RegOrZr w) where coe := fun r => .low (.reg r) w
attribute [coe] XRegOrSp.reg
attribute [coe] XRegOrXzr.reg
attribute [coe] RegOrSp.low
attribute [coe] RegOrZr.low

structure RegOrSpW where
  w : RegWidth
  reg : RegOrSp w
  deriving Repr, DecidableEq, Hashable, Lean.ToExpr

structure RegOrZrW where
  w : RegWidth
  reg : RegOrZr w
  deriving Repr, DecidableEq, Hashable, Lean.ToExpr

namespace RegOrSp
@[match_pattern] abbrev X0 := low (.reg .X0) .W64
@[match_pattern] abbrev X1 := low (.reg .X1) .W64
@[match_pattern] abbrev X2 := low (.reg .X2) .W64
@[match_pattern] abbrev X3 := low (.reg .X3) .W64
@[match_pattern] abbrev X4 := low (.reg .X4) .W64
@[match_pattern] abbrev X5 := low (.reg .X5) .W64
@[match_pattern] abbrev X6 := low (.reg .X6) .W64
@[match_pattern] abbrev X7 := low (.reg .X7) .W64
@[match_pattern] abbrev X8 := low (.reg .X8) .W64
@[match_pattern] abbrev X9 := low (.reg .X9) .W64
@[match_pattern] abbrev X10 := low (.reg .X10) .W64
@[match_pattern] abbrev X11 := low (.reg .X11) .W64
@[match_pattern] abbrev X12 := low (.reg .X12) .W64
@[match_pattern] abbrev X13 := low (.reg .X13) .W64
@[match_pattern] abbrev X14 := low (.reg .X14) .W64
@[match_pattern] abbrev X15 := low (.reg .X15) .W64
@[match_pattern] abbrev X16 := low (.reg .X16) .W64
@[match_pattern] abbrev X17 := low (.reg .X17) .W64
@[match_pattern] abbrev X18 := low (.reg .X18) .W64
@[match_pattern] abbrev X19 := low (.reg .X19) .W64
@[match_pattern] abbrev X20 := low (.reg .X20) .W64
@[match_pattern] abbrev X21 := low (.reg .X21) .W64
@[match_pattern] abbrev X22 := low (.reg .X22) .W64
@[match_pattern] abbrev X23 := low (.reg .X23) .W64
@[match_pattern] abbrev X24 := low (.reg .X24) .W64
@[match_pattern] abbrev X25 := low (.reg .X25) .W64
@[match_pattern] abbrev X26 := low (.reg .X26) .W64
@[match_pattern] abbrev X27 := low (.reg .X27) .W64
@[match_pattern] abbrev X28 := low (.reg .X28) .W64
@[match_pattern] abbrev X29 := low (.reg .X29) .W64
@[match_pattern] abbrev X30 := low (.reg .X30) .W64
@[match_pattern] abbrev SP := low .SP .W64

@[match_pattern] abbrev W0 := low (.reg .X0) .W32
@[match_pattern] abbrev W1 := low (.reg .X1) .W32
@[match_pattern] abbrev W2 := low (.reg .X2) .W32
@[match_pattern] abbrev W3 := low (.reg .X3) .W32
@[match_pattern] abbrev W4 := low (.reg .X4) .W32
@[match_pattern] abbrev W5 := low (.reg .X5) .W32
@[match_pattern] abbrev W6 := low (.reg .X6) .W32
@[match_pattern] abbrev W7 := low (.reg .X7) .W32
@[match_pattern] abbrev W8 := low (.reg .X8) .W32
@[match_pattern] abbrev W9 := low (.reg .X9) .W32
@[match_pattern] abbrev W10 := low (.reg .X10) .W32
@[match_pattern] abbrev W11 := low (.reg .X11) .W32
@[match_pattern] abbrev W12 := low (.reg .X12) .W32
@[match_pattern] abbrev W13 := low (.reg .X13) .W32
@[match_pattern] abbrev W14 := low (.reg .X14) .W32
@[match_pattern] abbrev W15 := low (.reg .X15) .W32
@[match_pattern] abbrev W16 := low (.reg .X16) .W32
@[match_pattern] abbrev W17 := low (.reg .X17) .W32
@[match_pattern] abbrev W18 := low (.reg .X18) .W32
@[match_pattern] abbrev W19 := low (.reg .X19) .W32
@[match_pattern] abbrev W20 := low (.reg .X20) .W32
@[match_pattern] abbrev W21 := low (.reg .X21) .W32
@[match_pattern] abbrev W22 := low (.reg .X22) .W32
@[match_pattern] abbrev W23 := low (.reg .X23) .W32
@[match_pattern] abbrev W24 := low (.reg .X24) .W32
@[match_pattern] abbrev W25 := low (.reg .X25) .W32
@[match_pattern] abbrev W26 := low (.reg .X26) .W32
@[match_pattern] abbrev W27 := low (.reg .X27) .W32
@[match_pattern] abbrev W28 := low (.reg .X28) .W32
@[match_pattern] abbrev W29 := low (.reg .X29) .W32
@[match_pattern] abbrev W30 := low (.reg .X30) .W32
@[match_pattern] abbrev WSP := low .SP .W32
end RegOrSp

namespace RegOrZr
@[match_pattern] abbrev X0 := low (.reg .X0) .W64
@[match_pattern] abbrev X1 := low (.reg .X1) .W64
@[match_pattern] abbrev X2 := low (.reg .X2) .W64
@[match_pattern] abbrev X3 := low (.reg .X3) .W64
@[match_pattern] abbrev X4 := low (.reg .X4) .W64
@[match_pattern] abbrev X5 := low (.reg .X5) .W64
@[match_pattern] abbrev X6 := low (.reg .X6) .W64
@[match_pattern] abbrev X7 := low (.reg .X7) .W64
@[match_pattern] abbrev X8 := low (.reg .X8) .W64
@[match_pattern] abbrev X9 := low (.reg .X9) .W64
@[match_pattern] abbrev X10 := low (.reg .X10) .W64
@[match_pattern] abbrev X11 := low (.reg .X11) .W64
@[match_pattern] abbrev X12 := low (.reg .X12) .W64
@[match_pattern] abbrev X13 := low (.reg .X13) .W64
@[match_pattern] abbrev X14 := low (.reg .X14) .W64
@[match_pattern] abbrev X15 := low (.reg .X15) .W64
@[match_pattern] abbrev X16 := low (.reg .X16) .W64
@[match_pattern] abbrev X17 := low (.reg .X17) .W64
@[match_pattern] abbrev X18 := low (.reg .X18) .W64
@[match_pattern] abbrev X19 := low (.reg .X19) .W64
@[match_pattern] abbrev X20 := low (.reg .X20) .W64
@[match_pattern] abbrev X21 := low (.reg .X21) .W64
@[match_pattern] abbrev X22 := low (.reg .X22) .W64
@[match_pattern] abbrev X23 := low (.reg .X23) .W64
@[match_pattern] abbrev X24 := low (.reg .X24) .W64
@[match_pattern] abbrev X25 := low (.reg .X25) .W64
@[match_pattern] abbrev X26 := low (.reg .X26) .W64
@[match_pattern] abbrev X27 := low (.reg .X27) .W64
@[match_pattern] abbrev X28 := low (.reg .X28) .W64
@[match_pattern] abbrev X29 := low (.reg .X29) .W64
@[match_pattern] abbrev X30 := low (.reg .X30) .W64
@[match_pattern] abbrev XZR := low .XZR .W64

@[match_pattern] abbrev W0 := low (.reg .X0) .W32
@[match_pattern] abbrev W1 := low (.reg .X1) .W32
@[match_pattern] abbrev W2 := low (.reg .X2) .W32
@[match_pattern] abbrev W3 := low (.reg .X3) .W32
@[match_pattern] abbrev W4 := low (.reg .X4) .W32
@[match_pattern] abbrev W5 := low (.reg .X5) .W32
@[match_pattern] abbrev W6 := low (.reg .X6) .W32
@[match_pattern] abbrev W7 := low (.reg .X7) .W32
@[match_pattern] abbrev W8 := low (.reg .X8) .W32
@[match_pattern] abbrev W9 := low (.reg .X9) .W32
@[match_pattern] abbrev W10 := low (.reg .X10) .W32
@[match_pattern] abbrev W11 := low (.reg .X11) .W32
@[match_pattern] abbrev W12 := low (.reg .X12) .W32
@[match_pattern] abbrev W13 := low (.reg .X13) .W32
@[match_pattern] abbrev W14 := low (.reg .X14) .W32
@[match_pattern] abbrev W15 := low (.reg .X15) .W32
@[match_pattern] abbrev W16 := low (.reg .X16) .W32
@[match_pattern] abbrev W17 := low (.reg .X17) .W32
@[match_pattern] abbrev W18 := low (.reg .X18) .W32
@[match_pattern] abbrev W19 := low (.reg .X19) .W32
@[match_pattern] abbrev W20 := low (.reg .X20) .W32
@[match_pattern] abbrev W21 := low (.reg .X21) .W32
@[match_pattern] abbrev W22 := low (.reg .X22) .W32
@[match_pattern] abbrev W23 := low (.reg .X23) .W32
@[match_pattern] abbrev W24 := low (.reg .X24) .W32
@[match_pattern] abbrev W25 := low (.reg .X25) .W32
@[match_pattern] abbrev W26 := low (.reg .X26) .W32
@[match_pattern] abbrev W27 := low (.reg .X27) .W32
@[match_pattern] abbrev W28 := low (.reg .X28) .W32
@[match_pattern] abbrev W29 := low (.reg .X29) .W32
@[match_pattern] abbrev W30 := low (.reg .X30) .W32
@[match_pattern] abbrev WZR := low .XZR .W32
end RegOrZr

/-! ### Constant, Extension, Shift, and Address Expressions -/

/-- Assembler constant expression, evaluated using 64-bit arithmetic. -/
inductive ConstExpr
  | label (_ : Label)
  | int64 (_ : Int64)
  | before_current_instruction | after_current_instruction
  | add (_ _ : ConstExpr) | sub (_ _ : ConstExpr)
  | pg_hi21 (_ : ConstExpr)
  | lo12 (_ : ConstExpr)
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

instance : Coe Label ConstExpr where coe := .label
instance : Coe Int64 ConstExpr where coe := .int64
instance {n} [OfNat Int64 n] : OfNat ConstExpr n where ofNat := .int64 (OfNat.ofNat n)
attribute [coe] ConstExpr.label
attribute [coe] ConstExpr.int64

/-- Extension types for extended-register arithmetic instructions (`UXTB`–`SXTX`). -/
inductive ExtendType | UXTB | SXTB | UXTH | SXTH | UXTW | SXTW | UXTX | SXTX
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

/-- Extension types for memory-addressing index registers (`UXTW`/`SXTW` on `Wn`, `UXTX`/`SXTX` on `Xn`). -/
inductive MemExtendType | UXTW | SXTW | UXTX | SXTX
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

/-- Left-shift amount `#0`–`#4` applied after extension in arithmetic instructions. -/
inductive ExtendAmount | E0 | E1 | E2 | E3 | E4
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

/-- Left-shift amount `#0`–`#3` applied to index registers in memory addressing. -/
inductive MemExtendAmount | E0 | E1 | E2 | E3
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

/-- Shift types for shifted-register operands (`ROR` is valid only in logical instructions). -/
inductive ShiftType | LSL | LSR | ASR | ROR
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

/-- Optional shift (`LSL #0` or `LSL #12`) for 12-bit immediate arithmetic operands. -/
inductive ImmShift | S0 | S12
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

/-- Shift amounts (`#0`, `#16`, and `#32`/`#48` for `.W64`) for wide immediate moves (`MOVZ`/`MOVK`/`MOVN`). -/
inductive MovShift : RegWidth → Type
  | LSL0 {w}  : MovShift w
  | LSL16 {w} : MovShift w
  | LSL32     : MovShift .W64
  | LSL48     : MovShift .W64
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

@[kstep, simp, reducible] def MovShift.toNat {w} : MovShift w → Nat
  | .LSL0  => 0
  | .LSL16 => 16
  | .LSL32 => 32
  | .LSL48 => 48

/-- Pre-indexed (`[Xn, #imm]!`) or post-indexed (`[Xn], #imm`) writeback mode. -/
inductive Index | Pre | Post
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

/-- Extension type and shift amount for arithmetic instructions. -/
structure Extend where
  type : ExtendType
  amount : ExtendAmount
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

/-- Extension type and shift amount for memory index registers. -/
structure MemExtend where
  type : MemExtendType
  amount : MemExtendAmount
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

/-- Extended register operand for arithmetic instructions (`Xm, <extend> #<amount>`). -/
structure ExtRegExpr where
  reg : RegOrZrW
  ext : Extend
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

/-- Extended index-register operand for memory addressing (`[Xn, Xm, <extend> #<amount>]`). -/
structure MemExtRegExpr where
  reg : RegOrZrW
  ext : MemExtend
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

/-- 12-bit unsigned immediate operand (`[0, 4095]`) with optional `LSL #0` or `LSL #12` shift. -/
structure ImmExpr where
  imm : ConstExpr
  shift : ImmShift
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

/-- Shifted register operand (`Xm, <shift> #<amount>`). -/
structure ShiftRegExpr (w : RegWidth) where
  reg : RegOrZr w
  amount : Int64
  shift : ShiftType
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

instance {w} : Coe (RegOrZr w) (ShiftRegExpr w) where
  coe r := { reg := r, amount := 0, shift := .LSL }

/-- Immediate memory offset with optional pre/post-index writeback. -/
structure ImmAddrExpr where
  imm : ConstExpr
  index : Option Index
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

/-- PC-relative label address (`ldr Xt, label`). -/
structure LitAddrExpr where
  label : Label
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

/-- PC-relative literal pool constant (`ldr Xt, =expr`). -/
structure LitPoolExpr where
  expr : ConstExpr
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

inductive AddrOff | imm (_ : ImmAddrExpr) | reg (_ : MemExtRegExpr)
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr
instance : Coe ImmAddrExpr AddrOff where coe := .imm
instance : Coe MemExtRegExpr AddrOff where coe := .reg
instance : Coe ConstExpr ImmAddrExpr where coe := fun e => { imm := e, index := none }
instance : Coe ConstExpr AddrOff where coe := fun e => .imm { imm := e, index := none }
instance : Coe Int64 ImmAddrExpr where coe := fun i => { imm := .int64 i, index := none }
instance : Coe Int64 AddrOff where coe := fun i => .imm { imm := .int64 i, index := none }
instance {n} [OfNat Int64 n] : OfNat ImmAddrExpr n where
  ofNat := { imm := .int64 (OfNat.ofNat n), index := none }
instance {n} [OfNat Int64 n] : OfNat AddrOff n where
  ofNat := .imm { imm := .int64 (OfNat.ofNat n), index := none }
attribute [coe] AddrOff.imm
attribute [coe] AddrOff.reg

inductive Literal | addr (_ : LitAddrExpr) | pool (_ : LitPoolExpr)
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr
instance : Coe LitAddrExpr Literal where coe := .addr
instance : Coe LitPoolExpr Literal where coe := .pool
attribute [coe] Literal.addr
attribute [coe] Literal.pool

structure AddrExpr where
  base : RegOrSp .W64
  off : AddrOff
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

/-- Unscaled 9-bit signed offset (`[-256, 255]`) for `LDUR`/`STUR`. -/
structure UnscaledAddrExpr where
  base : RegOrSp .W64
  imm : ConstExpr
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

inductive AddrOrLit | addr (_ : AddrExpr) | lit (_ : Literal)
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr
instance : Coe AddrExpr AddrOrLit where coe := .addr
instance : Coe Literal AddrOrLit where coe := .lit
attribute [coe] AddrOrLit.addr
attribute [coe] AddrOrLit.lit

inductive ExtOrImmReg | ext (_ : ExtRegExpr) | imm (_ : ImmExpr)
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr
instance : Coe ExtRegExpr ExtOrImmReg where coe := .ext
instance : Coe ImmExpr ExtOrImmReg where coe := .imm
instance : Coe ConstExpr ImmExpr where coe := fun e => { imm := e, shift := .S0 }
instance : Coe ConstExpr ExtOrImmReg where coe := fun e => .imm { imm := e, shift := .S0 }
instance : Coe Int64 ImmExpr where coe := fun i => { imm := .int64 i, shift := .S0 }
instance : Coe Int64 ExtOrImmReg where coe := fun i => .imm { imm := .int64 i, shift := .S0 }
instance {n} [OfNat Int64 n] : OfNat ImmExpr n where
  ofNat := { imm := .int64 (OfNat.ofNat n), shift := .S0 }
instance {n} [OfNat Int64 n] : OfNat ExtOrImmReg n where
  ofNat := .imm { imm := .int64 (OfNat.ofNat n), shift := .S0 }
attribute [coe] ExtOrImmReg.ext
attribute [coe] ExtOrImmReg.imm

/-! ### Condition Codes -/

inductive CondCode | EQ | NE | CS | CC | MI | PL | VS | VC | HI | LS | GE | LT | GT | LE | AL | NV
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr
abbrev CondCode.HS := CondCode.CS
abbrev CondCode.LO := CondCode.CC

def CondCode.invert : CondCode → CondCode
  | .EQ => .NE | .NE => .EQ
  | .CS => .CC | .CC => .CS
  | .MI => .PL | .PL => .MI
  | .VS => .VC | .VC => .VS
  | .HI => .LS | .LS => .HI
  | .GE => .LT | .LT => .GE
  | .GT => .LE | .LE => .GT
  | .AL => .NV | .NV => .AL

/-! ### Operations, Instructions, and Directives -/

inductive Operation : RegWidth → Type
  -- Loads and stores
  | LDR {w} (dst : RegOrZr w) (src : AddrOrLit) : Operation w
  | STR {w} (src : RegOrZr w) (dst : AddrExpr) : Operation w
  | LDUR {w} (dst : RegOrZr w) (src : UnscaledAddrExpr) : Operation w
  | STUR {w} (src : RegOrZr w) (dst : UnscaledAddrExpr) : Operation w
  | LDP {w} (dst1 : RegOrZr w) (dst2 : RegOrZr w) (src : AddrExpr) : Operation w
  | STP {w} (src1 : RegOrZr w) (src2 : RegOrZr w) (dst : AddrExpr) : Operation w
  | LDRB (dst : RegOrZr .W32) (src : AddrExpr) : Operation .W32
  | LDURB (dst : RegOrZr .W32) (src : UnscaledAddrExpr) : Operation .W32
  | STRB (src : RegOrZr .W32) (dst : AddrExpr) : Operation .W32
  | STURB (src : RegOrZr .W32) (dst : UnscaledAddrExpr) : Operation .W32
  | LDRSB {w} (dst : RegOrZr w) (src : AddrExpr) : Operation w
  | LDURSB {w} (dst : RegOrZr w) (src : UnscaledAddrExpr) : Operation w
  | LDRH (dst : RegOrZr .W32) (src : AddrExpr) : Operation .W32
  | LDURH (dst : RegOrZr .W32) (src : UnscaledAddrExpr) : Operation .W32
  | STRH (src : RegOrZr .W32) (dst : AddrExpr) : Operation .W32
  | STURH (src : RegOrZr .W32) (dst : UnscaledAddrExpr) : Operation .W32
  | LDRSH {w} (dst : RegOrZr w) (src : AddrExpr) : Operation w
  | LDURSH {w} (dst : RegOrZr w) (src : UnscaledAddrExpr) : Operation w
  | LDRSW (dst : RegOrZr .W64) (src : AddrOrLit) : Operation .W64
  | LDURSW (dst : RegOrZr .W64) (src : UnscaledAddrExpr) : Operation .W64
  | LDPSW (dst1 : RegOrZr .W64) (dst2 : RegOrZr .W64) (src : AddrExpr) : Operation .W64
  -- Arithmetic (extended/immediate `_e` and shifted-register `_s` forms)
  | ADD_e {w} (dst : RegOrSp w) (src1 : RegOrSp w) (src2 : ExtOrImmReg) : Operation w
  | ADD_s {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : ShiftRegExpr w) : Operation w
  | ADDS_e {w} (dst : RegOrZr w) (src1 : RegOrSp w) (src2 : ExtOrImmReg) : Operation w
  | ADDS_s {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : ShiftRegExpr w) : Operation w
  | SUB_e {w} (dst : RegOrSp w) (src1 : RegOrSp w) (src2 : ExtOrImmReg) : Operation w
  | SUB_s {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : ShiftRegExpr w) : Operation w
  | SUBS_e {w} (dst : RegOrZr w) (src1 : RegOrSp w) (src2 : ExtOrImmReg) : Operation w
  | SUBS_s {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : ShiftRegExpr w) : Operation w
  -- Carry arithmetic
  | ADC {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : RegOrZr w) : Operation w
  | ADCS {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : RegOrZr w) : Operation w
  | SBC {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : RegOrZr w) : Operation w
  | SBCS {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : RegOrZr w) : Operation w
  -- Division
  | SDIV {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : RegOrZr w) : Operation w
  | UDIV {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : RegOrZr w) : Operation w
  -- Multiply
  | MADD {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : RegOrZr w) (src3 : RegOrZr w) : Operation w
  | MSUB {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : RegOrZr w) (src3 : RegOrZr w) : Operation w
  | SMULH (dst : RegOrZr .W64) (src1 : RegOrZr .W64) (src2 : RegOrZr .W64) : Operation .W64
  | UMULH (dst : RegOrZr .W64) (src1 : RegOrZr .W64) (src2 : RegOrZr .W64) : Operation .W64
  | SMADDL (dst : RegOrZr .W64) (src1 : RegOrZr .W32) (src2 : RegOrZr .W32) (src3 : RegOrZr .W64) : Operation .W64
  | UMADDL (dst : RegOrZr .W64) (src1 : RegOrZr .W32) (src2 : RegOrZr .W32) (src3 : RegOrZr .W64) : Operation .W64
  | SMSUBL (dst : RegOrZr .W64) (src1 : RegOrZr .W32) (src2 : RegOrZr .W32) (src3 : RegOrZr .W64) : Operation .W64
  | UMSUBL (dst : RegOrZr .W64) (src1 : RegOrZr .W32) (src2 : RegOrZr .W32) (src3 : RegOrZr .W64) : Operation .W64
  -- Logic (immediate `_i` and shifted-register `_s` forms)
  | AND_i  {w} (dst : RegOrSp w) (src1 : RegOrZr w) (imm : ConstExpr) : Operation w
  | AND_s  {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : ShiftRegExpr w) : Operation w
  | ANDS_i {w} (dst : RegOrZr w) (src1 : RegOrZr w) (imm : ConstExpr) : Operation w
  | ANDS_s {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : ShiftRegExpr w) : Operation w
  | ORR_i  {w} (dst : RegOrSp w) (src1 : RegOrZr w) (imm : ConstExpr) : Operation w
  | ORR_s  {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : ShiftRegExpr w) : Operation w
  | ORN_s  {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : ShiftRegExpr w) : Operation w
  | EOR_i  {w} (dst : RegOrSp w) (src1 : RegOrZr w) (imm : ConstExpr) : Operation w
  | EOR_s  {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : ShiftRegExpr w) : Operation w
  | EON_s  {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : ShiftRegExpr w) : Operation w
  | BIC_s  {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : ShiftRegExpr w) : Operation w
  | BICS_s {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : ShiftRegExpr w) : Operation w
  -- Bitfield and bit manipulation
  | BFM  {w} (dst : RegOrZr w) (src : RegOrZr w) (immr : Nat) (imms : Nat) : Operation w
  | SBFM {w} (dst : RegOrZr w) (src : RegOrZr w) (immr : Nat) (imms : Nat) : Operation w
  | UBFM {w} (dst : RegOrZr w) (src : RegOrZr w) (immr : Nat) (imms : Nat) : Operation w
  | CLZ  {w} (dst : RegOrZr w) (src : RegOrZr w) : Operation w
  | CLS  {w} (dst : RegOrZr w) (src : RegOrZr w) : Operation w
  | RBIT {w} (dst : RegOrZr w) (src : RegOrZr w) : Operation w
  | REV  {w} (dst : RegOrZr w) (src : RegOrZr w) : Operation w
  | REV16 {w} (dst : RegOrZr w) (src : RegOrZr w) : Operation w
  | REV32 (dst : RegOrZr .W64) (src : RegOrZr .W64) : Operation .W64
  | EXTR {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : RegOrZr w) (lsb : Nat) : Operation w
  -- Move wide immediates
  | MOVZ {w} (dst : RegOrZr w) (imm : ConstExpr) (shift : MovShift w) : Operation w
  | MOVK {w} (dst : RegOrZr w) (imm : ConstExpr) (shift : MovShift w) : Operation w
  | MOVN {w} (dst : RegOrZr w) (imm : ConstExpr) (shift : MovShift w) : Operation w
  -- Variable shifts and rotates
  | LSLV {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : RegOrZr w) : Operation w
  | LSRV {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : RegOrZr w) : Operation w
  | ASRV {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : RegOrZr w) : Operation w
  | RORV {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : RegOrZr w) : Operation w
  -- Conditional select
  | CSEL {w} (dst : RegOrZr w) (src1 src2 : RegOrZr w) (cond : CondCode) : Operation w
  | CSINC {w} (dst : RegOrZr w) (src1 src2 : RegOrZr w) (cond : CondCode) : Operation w
  | CSINV {w} (dst : RegOrZr w) (src1 src2 : RegOrZr w) (cond : CondCode) : Operation w
  | CSNEG {w} (dst : RegOrZr w) (src1 src2 : RegOrZr w) (cond : CondCode) : Operation w
  -- Conditional compare
  | CCMP_reg {w} (src1 : RegOrZr w) (src2 : RegOrZr w) (nzcv : Nat) (cond : CondCode) : Operation w
  | CCMP_imm {w} (src1 : RegOrZr w) (imm : Nat) (nzcv : Nat) (cond : CondCode) : Operation w
  | CCMN_reg {w} (src1 : RegOrZr w) (src2 : RegOrZr w) (nzcv : Nat) (cond : CondCode) : Operation w
  | CCMN_imm {w} (src1 : RegOrZr w) (imm : Nat) (nzcv : Nat) (cond : CondCode) : Operation w
  -- PC-relative addressing
  | ADR (dst : RegOrZr .W64) (target : ConstExpr) : Operation .W64
  | ADRP (dst : RegOrZr .W64) (target : ConstExpr) : Operation .W64
  -- Control flow
  | B (target : ConstExpr) : Operation .W64
  | B_cond (cond : CondCode) (target : ConstExpr) : Operation .W64
  | BL (target : ConstExpr) : Operation .W64
  | BLR (target : RegOrZr .W64) : Operation .W64
  | BR (target : RegOrZr .W64) : Operation .W64
  | RET (target : RegOrZr .W64) : Operation .W64
  | CBZ {w} (reg : RegOrZr w) (target : ConstExpr) : Operation w
  | CBNZ {w} (reg : RegOrZr w) (target : ConstExpr) : Operation w
  | TBZ {w} (reg : RegOrZr w) (bit : Nat) (target : ConstExpr) : Operation w
  | TBNZ {w} (reg : RegOrZr w) (bit : Nat) (target : ConstExpr) : Operation w
  | NOP {w} : Operation w
  deriving Repr, DecidableEq, Hashable, Lean.ToExpr

structure Instr where
  operation_size : RegWidth
  operation : Operation operation_size
  deriving Repr, DecidableEq, Hashable, Lean.ToExpr

abbrev Directive := Kraken.Directive Instr ConstExpr
abbrev Program := List Directive
abbrev Executable := Kraken.Executable Instr ConstExpr
