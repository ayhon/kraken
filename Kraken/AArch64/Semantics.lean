module

public import Kraken.AArch64.Syntax
public meta import Kraken.AArch64.Syntax
import Kraken.Attribute
public import Kraken.Mem
public meta import Kraken.Mem
public import Kraken.Semantics
public meta import Kraken.Semantics
public import Kraken.Frame
public import Lean.ToExpr
meta import Lean.Elab.Deriving.ToExpr

/-!
# AArch64 Instruction Semantics

Operational semantics for AArch64 instructions, registers, status flags, operands, and directives,
together with value-level flag projections (`@[kcond]`) and carry-chain limb identities.
-/

@[expose] public section

/-! ### Registers and Register File -/

namespace RegOrSp
@[kstep] def base {w} (r : RegOrSp w) : XRegOrSp := match r with
  | .low r _ => r
end RegOrSp

namespace RegOrZr
@[kstep] def base {w} (r : RegOrZr w) : XRegOrXzr := match r with
  | .low r _ => r
end RegOrZr

structure Reg64s where
  X0 : UInt64 := 0
  X1 : UInt64 := 0
  X2 : UInt64 := 0
  X3 : UInt64 := 0
  X4 : UInt64 := 0
  X5 : UInt64 := 0
  X6 : UInt64 := 0
  X7 : UInt64 := 0
  X8 : UInt64 := 0
  X9 : UInt64 := 0
  X10 : UInt64 := 0
  X11 : UInt64 := 0
  X12 : UInt64 := 0
  X13 : UInt64 := 0
  X14 : UInt64 := 0
  X15 : UInt64 := 0
  X16 : UInt64 := 0
  X17 : UInt64 := 0
  X18 : UInt64 := 0
  X19 : UInt64 := 0
  X20 : UInt64 := 0
  X21 : UInt64 := 0
  X22 : UInt64 := 0
  X23 : UInt64 := 0
  X24 : UInt64 := 0
  X25 : UInt64 := 0
  X26 : UInt64 := 0
  X27 : UInt64 := 0
  X28 : UInt64 := 0
  X29 : UInt64 := 0
  X30 : UInt64 := 0
  SP : UInt64 := 0
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

@[kstep] def Reg64s.getXReg (s : Reg64s) (r : XReg) := match r with
  |  .X0 =>  s.X0 |  .X1 =>  s.X1 |  .X2 =>  s.X2 |  .X3 =>  s.X3
  |  .X4 =>  s.X4 |  .X5 =>  s.X5 |  .X6 =>  s.X6 |  .X7 =>  s.X7
  |  .X8 =>  s.X8 |  .X9 =>  s.X9 | .X10 => s.X10 | .X11 => s.X11
  | .X12 => s.X12 | .X13 => s.X13 | .X14 => s.X14 | .X15 => s.X15
  | .X16 => s.X16 | .X17 => s.X17 | .X18 => s.X18 | .X19 => s.X19
  | .X20 => s.X20 | .X21 => s.X21 | .X22 => s.X22 | .X23 => s.X23
  | .X24 => s.X24 | .X25 => s.X25 | .X26 => s.X26 | .X27 => s.X27
  | .X28 => s.X28 | .X29 => s.X29 | .X30 => s.X30

@[kstep] def Reg64s.getRegOrSp64 (s : Reg64s) (r : XRegOrSp) : RegWidth.W64.type := UInt64.toBitVec (match r with
  | .reg r => s.getXReg r
  | .SP => s.SP)

@[kstep] def Reg64s.getRegOrZr64 (s : Reg64s) (r : XRegOrXzr) : RegWidth.W64.type := UInt64.toBitVec (match r with
  | .reg r => s.getXReg r
  | .XZR => 0)

@[kstep] def Reg64s.setXReg (regs : Reg64s) (r : XReg) (v : RegWidth.W64.type) : Reg64s :=
  match r with
  |  .X0 => { regs with  X0 := UInt64.ofBitVec v } |  .X1 => { regs with  X1 := UInt64.ofBitVec v }
  |  .X2 => { regs with  X2 := UInt64.ofBitVec v } |  .X3 => { regs with  X3 := UInt64.ofBitVec v }
  |  .X4 => { regs with  X4 := UInt64.ofBitVec v } |  .X5 => { regs with  X5 := UInt64.ofBitVec v }
  |  .X6 => { regs with  X6 := UInt64.ofBitVec v } |  .X7 => { regs with  X7 := UInt64.ofBitVec v }
  |  .X8 => { regs with  X8 := UInt64.ofBitVec v } |  .X9 => { regs with  X9 := UInt64.ofBitVec v }
  | .X10 => { regs with X10 := UInt64.ofBitVec v } | .X11 => { regs with X11 := UInt64.ofBitVec v }
  | .X12 => { regs with X12 := UInt64.ofBitVec v } | .X13 => { regs with X13 := UInt64.ofBitVec v }
  | .X14 => { regs with X14 := UInt64.ofBitVec v } | .X15 => { regs with X15 := UInt64.ofBitVec v }
  | .X16 => { regs with X16 := UInt64.ofBitVec v } | .X17 => { regs with X17 := UInt64.ofBitVec v }
  | .X18 => { regs with X18 := UInt64.ofBitVec v } | .X19 => { regs with X19 := UInt64.ofBitVec v }
  | .X20 => { regs with X20 := UInt64.ofBitVec v } | .X21 => { regs with X21 := UInt64.ofBitVec v }
  | .X22 => { regs with X22 := UInt64.ofBitVec v } | .X23 => { regs with X23 := UInt64.ofBitVec v }
  | .X24 => { regs with X24 := UInt64.ofBitVec v } | .X25 => { regs with X25 := UInt64.ofBitVec v }
  | .X26 => { regs with X26 := UInt64.ofBitVec v } | .X27 => { regs with X27 := UInt64.ofBitVec v }
  | .X28 => { regs with X28 := UInt64.ofBitVec v } | .X29 => { regs with X29 := UInt64.ofBitVec v }
  | .X30 => { regs with X30 := UInt64.ofBitVec v }

@[kstep] def Reg64s.setRegOrSp64 (regs : Reg64s) (r : XRegOrSp) (v : RegWidth.W64.type) : Reg64s :=
  match r with
  | .reg r => regs.setXReg r v
  | .SP => { regs with SP := UInt64.ofBitVec v }

@[kstep] def Reg64s.setRegOrZr64 (regs : Reg64s) (r : XRegOrXzr) (v : RegWidth.W64.type) : Reg64s :=
  match r with
  | .reg r => regs.setXReg r v
  | .XZR => regs

@[kstep] def Reg64s.getRegOrSp (s : Reg64s) {w} (r : RegOrSp w) : w.type := match r with
  | .low r .W64 => s.getRegOrSp64 r
  | .low r .W32 => (s.getRegOrSp64 r).take 32

@[kstep] def Reg64s.getRegOrZr (s : Reg64s) {w} (r : RegOrZr w) : w.type := match r with
  | .low r .W64 => s.getRegOrZr64 r
  | .low r .W32 => (s.getRegOrZr64 r).take 32

@[kstep] def Reg64s.setRegOrSp (s : Reg64s) {w} (r : RegOrSp w) (v : w.type) : Reg64s := match r with
  | .low r .W64 => s.setRegOrSp64 r v
  | .low r .W32 => s.setRegOrSp64 r (v.zeroExtend _)

@[kstep] def Reg64s.setRegOrZr (s : Reg64s) {w} (r : RegOrZr w) (v : w.type) : Reg64s := match r with
  | .low r .W64 => s.setRegOrZr64 r v
  | .low r .W32 => s.setRegOrZr64 r (v.zeroExtend _)

/-- Register file view of `Reg64s` for frame ("modifies") clauses: `r' ≡ r except [X13, SP]`. -/
instance : Kraken.RegFile Reg64s where
  Name := XRegOrSp
  get r n := match n with
    | .reg x => r.getXReg x
    | .SP => r.SP
  names := [.SP,
    .reg .X0, .reg .X1, .reg .X2, .reg .X3, .reg .X4, .reg .X5, .reg .X6, .reg .X7,
    .reg .X8, .reg .X9, .reg .X10, .reg .X11, .reg .X12, .reg .X13, .reg .X14, .reg .X15,
    .reg .X16, .reg .X17, .reg .X18, .reg .X19, .reg .X20, .reg .X21, .reg .X22, .reg .X23,
    .reg .X24, .reg .X25, .reg .X26, .reg .X27, .reg .X28, .reg .X29, .reg .X30]
  mem_names n := by rcases n with x | _ <;> (try cases x) <;> simp

/-- AAPCS64 callee-saved general-purpose registers (`X19`–`X29`). -/
@[grind]
def Reg64s.CalleeSavedEq (r r₀ : Reg64s) : Prop :=
  r.X19 = r₀.X19 ∧
  r.X20 = r₀.X20 ∧
  r.X21 = r₀.X21 ∧
  r.X22 = r₀.X22 ∧
  r.X23 = r₀.X23 ∧
  r.X24 = r₀.X24 ∧
  r.X25 = r₀.X25 ∧
  r.X26 = r₀.X26 ∧
  r.X27 = r₀.X27 ∧
  r.X28 = r₀.X28 ∧
  r.X29 = r₀.X29

@[simp, ksimp, grind .]
theorem Reg64s.CalleeSavedEq_refl (r : Reg64s) : r.CalleeSavedEq r :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Reg64s.CalleeSavedEq.symm {r₁ r₂ : Reg64s} (h : r₁.CalleeSavedEq r₂) :
    r₂.CalleeSavedEq r₁ := by
  grind

theorem Reg64s.CalleeSavedEq.trans {r₁ r₂ r₃ : Reg64s}
    (h₁ : r₁.CalleeSavedEq r₂) (h₂ : r₂.CalleeSavedEq r₃) :
    r₁.CalleeSavedEq r₃ := by
  grind

/-! ### Status Flags -/

structure StatusFlags where
  n : Bool
  z : Bool
  c : Bool
  v : Bool
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

structure StatusFlags.from_result.Remaining where
  c : Bool
  v : Bool
  deriving Repr, BEq, DecidableEq

@[kstep, simp] def StatusFlags.from_result {w} (result : BitVec w) (f : from_result.Remaining) : StatusFlags :=
  { n := result.msb
    z := result == BitVec.zero _
    c := f.c
    v := f.v }

/-- Flag-setting arithmetic abstraction boundary: `kstep` keeps these unexpanded so symbolic states
record e.g. `status := StatusFlags.subs X2.toBitVec X3.toBitVec`, and `@[kcond]` projection lemmas
reduce individual flags to decided value-level propositions when read by a condition code or carry-in. -/
def StatusFlags.adds {w} (a b : BitVec w) : StatusFlags :=
  let res := a + b
  StatusFlags.from_result res {
    c := res.unsigned != a.unsigned + b.unsigned
    v := res.signed != a.signed + b.signed }

/-- Flags of `adcs`: `res = a + b + cin`. -/
def StatusFlags.adcs {w} (a b : BitVec w) (cin : Bool) : StatusFlags :=
  let res := a + b + BitVec.ofNat w cin.toNat
  let cin_int : Int := if cin then 1 else 0
  StatusFlags.from_result res {
    c := res.unsigned != a.unsigned + b.unsigned + cin_int
    v := res.signed != a.signed + b.signed + cin_int }

/-- Flags of `subs`/`cmp`: `res = a - b`. -/
def StatusFlags.subs {w} (a b : BitVec w) : StatusFlags :=
  let res := a - b
  StatusFlags.from_result res {
    c := res.unsigned == a.unsigned - b.unsigned
    v := res.signed != a.signed - b.signed }

/-- Flags of `sbcs`: `res = a - b - (1 - cin)`. -/
def StatusFlags.sbcs {w} (a b : BitVec w) (cin : Bool) : StatusFlags :=
  let res := a - b - BitVec.ofNat w (!cin).toNat
  let bin : Int := if cin then 0 else 1
  StatusFlags.from_result res {
    c := res.unsigned == a.unsigned - b.unsigned - bin
    v := res.signed != a.signed - b.signed - bin }

/-- Flags of the flag-setting logical operations (`ands`, `bics`, `tst`): `c = v = 0`. -/
def StatusFlags.logical {w} (res : BitVec w) : StatusFlags :=
  StatusFlags.from_result res { c := false, v := false }

def StatusFlags.ofNat (nzcv : Nat) : StatusFlags :=
  { n := (nzcv &&& 8) != 0
    z := (nzcv &&& 4) != 0
    c := (nzcv &&& 2) != 0
    v := (nzcv &&& 1) != 0 }

@[kstep, simp] def CondCode.interp (cc : CondCode) (s : StatusFlags) : Bool := match cc with
  | .EQ => s.z
  | .NE => !s.z
  | .CS => s.c
  | .CC => !s.c
  | .MI => s.n
  | .PL => !s.n
  | .VS => s.v
  | .VC => !s.v
  | .HI => s.c && !s.z
  | .LS => !s.c || s.z
  | .GE => s.n == s.v
  | .LT => s.n != s.v
  | .GT => !s.z && s.n == s.v
  | .LE => s.z || s.n != s.v
  | .AL => true
  | .NV => true

/-! ### Machine State and Memory Helpers -/

structure MachineData where
  regs : Reg64s := {}
  status : StatusFlags := .mk false false false false
  dmem : DataMem := ∅
  deriving Repr, BEq, DecidableEq

@[reducible]
instance : HasDataMem MachineData where
  dmem s := s.dmem
  withDmem s dmem := { s with dmem }

instance (w : RegWidth) : NondetSupportingType w.type where
  from_hash h := h.toBitVec.setWidth w.bits

instance : NondetSupportingType StatusFlags where
  from_hash h := let h := h.toBitVec; (.mk h[0] h[1] h[2] h[3])

abbrev MachineState := Kraken.MachineState MachineData
abbrev Effects := Kraken.Effects MachineData

@[kstep] def MachineData.setRegOrSp (s : MachineData) {w} (r : RegOrSp w) (v : w.type) (ret : MachineData → Effects) : Effects :=
  ret { s with regs := s.regs.setRegOrSp r v }

@[kstep] def MachineData.setRegOrZr (s : MachineData) {w} (r : RegOrZr w) (v : w.type) (ret : MachineData → Effects) : Effects :=
  ret { s with regs := s.regs.setRegOrZr r v }

/-! ### Operand and Address Evaluation -/

def RegOrSp.interp {w} (r : RegOrSp w) (s : MachineData) (_ : Std.Rco Int64)
  (ret : w.type → MachineData → Effects) : Effects :=
  ret (s.regs.getRegOrSp r) s

def RegOrZr.interp {w} (r : RegOrZr w) (s : MachineData) (_ : Std.Rco Int64)
  (ret : w.type → MachineData → Effects) : Effects :=
  ret (s.regs.getRegOrZr r) s

@[kstep] def ConstExpr.interp [Labels] : ConstExpr → Std.Rco Int64 → Int64
  | .label l, _ => Labels.label l
  | .int64 i, _ => i
  | .before_current_instruction, r => r.lower
  | .after_current_instruction, r => r.upper
  | .add e1 e2, p => e1.interp p + e2.interp p
  | .sub e1 e2, p => e1.interp p - e2.interp p
  | .pg_hi21 e, p =>
    let val := BitVec.ofInt 64 (Int64.toInt (e.interp p))
    let page := val &&& ~~~0xFFF#64
    Int64.ofNat page.toNat
  | .lo12 e, p =>
    let val := BitVec.ofInt 64 (Int64.toInt (e.interp p))
    let lo := val &&& 0xFFF#64
    Int64.ofNat lo.toNat

@[kstep] def ConstExpr.evalBranchTarget [Labels] (target : ConstExpr) (p : Std.Rco Int64) : Int64 :=
  match target with
  | .int64 imm => p.lower + imm
  | _ => target.interp p

@[kstep] def BitVec.apply_extend (v : BitVec 64) (ext : Extend) :=
  let extended := match ext.type with
               | .UXTB => (v.take Width.W8.bits).unsigned
               | .SXTB => (v.take Width.W8.bits).signed
               | .UXTH => (v.take Width.W16.bits).unsigned
               | .SXTH => (v.take Width.W16.bits).signed
               | .UXTW => (v.take Width.W32.bits).unsigned
               | .SXTW => (v.take Width.W32.bits).signed
               | .UXTX => v.unsigned
               | .SXTX => v.signed
  match ext.amount with
  | .E0 => extended
  | .E1 => extended <<< 1
  | .E2 => extended <<< 2
  | .E3 => extended <<< 3
  | .E4 => extended <<< 4

@[kstep] def BitVec.apply_mem_extend (v : BitVec 64) (ext : MemExtend) :=
  let extended := match ext.type with
               | .UXTW => (v.take Width.W32.bits).unsigned
               | .SXTW => (v.take Width.W32.bits).signed
               | .UXTX => v.unsigned
               | .SXTX => v.signed
  match ext.amount with
  | .E0 => extended
  | .E1 => extended <<< 1
  | .E2 => extended <<< 2
  | .E3 => extended <<< 3

@[kstep] def ExtRegExpr.interp (er : ExtRegExpr) (s : Reg64s) (_ : Std.Rco Int64) :=
  (s.getRegOrZr64 er.reg.reg.base).apply_extend er.ext

@[kstep] def MemExtRegExpr.interp (er : MemExtRegExpr) (s : Reg64s) (_ : Std.Rco Int64) :=
  (s.getRegOrZr64 er.reg.reg.base).apply_mem_extend er.ext

@[kstep] def ExtOrImmReg.interp [Labels] {w : RegWidth} (expr : ExtOrImmReg) (s : Reg64s) (p : Std.Rco Int64) : w.type :=
  match expr with
  | .ext e =>
    BitVec.ofInt w.bits (e.interp s p)
  | .imm i =>
    let imm := Int64.toInt (i.imm.interp p)
    match i.shift with
    | .S0 => BitVec.ofInt w.bits imm
    | .S12 => BitVec.ofInt w.bits (imm <<< 12)

@[kstep] def ShiftRegExpr.interp {w} (expr : ShiftRegExpr w) (s : Reg64s) (_ : Std.Rco Int64) : w.type :=
  match expr.shift with
  | .LSL => (s.getRegOrZr expr.reg) <<< (Int64.toInt expr.amount).toNat
  | .LSR => (s.getRegOrZr expr.reg).ushiftRight (Int64.toInt expr.amount).toNat
  | .ASR => (s.getRegOrZr expr.reg).sshiftRight (Int64.toInt expr.amount).toNat
  | .ROR => (s.getRegOrZr expr.reg).rotateRight (Int64.toInt expr.amount).toNat

/-- AArch64 mandates 16-byte alignment when accessing memory through `SP`. -/
@[kstep] def RegOrSp.checkSPAlignment (base : RegOrSp .W64) (s : MachineData) (ok : Unit → Effects) : Effects :=
  match base with
  | .SP =>
    if s.regs.getRegOrSp .SP % 16#64 != 0#64 then
      .unaligned (s.regs.getRegOrSp .SP) 16
    else
      ok ()
  | _ => ok ()

@[kstep] def AddrExpr.eval [Labels] (mem : AddrExpr) (s : MachineData) (p : Std.Rco Int64) : BitVec 64 × MachineData :=
  let base := (s.regs.getRegOrSp mem.base).signed
  match mem.off with
  | .reg r =>
    let off := r.interp s.regs p
    (BitVec.ofInt 64 (base + off), s)
  | .imm i =>
    let off := Int64.toInt (i.imm.interp p)
    let addr := match i.index with
      | some .Post => BitVec.ofInt 64 base
      | _ => BitVec.ofInt 64 (base + off)
    let s' := match i.index with
      | some _ => { s with regs := s.regs.setRegOrSp mem.base (BitVec.ofInt 64 (base + off)) }
      | none => s
    (addr, s')

@[kstep] def AddrExpr.checkSPAlignment (mem : AddrExpr) (s : MachineData) (ok : Unit → Effects) : Effects :=
  mem.base.checkSPAlignment s ok

@[kstep] def AddrExpr.interpLoad [Labels] {w : Width} (mem : AddrExpr) (s : MachineData) (p : Std.Rco Int64) (ret : w.type → MachineData → Effects) :=
  mem.checkSPAlignment s (fun _unit =>
    let (addr, s') := mem.eval s p
    MachineData.load s' addr w ret)

@[kstep] def AddrExpr.interpStore [Labels] {w : Width} (mem : AddrExpr) (s : MachineData) (p : Std.Rco Int64)
    (val : w.type) (next : MachineData → Effects) : Effects :=
  mem.checkSPAlignment s (fun _unit =>
    let (addr, s') := mem.eval s p
    MachineData.store s' addr (w := w) val next)

@[kstep] def UnscaledAddrExpr.eval [Labels] (mem : UnscaledAddrExpr) (s : MachineData) (p : Std.Rco Int64) : BitVec 64 :=
  let base := (s.regs.getRegOrSp mem.base).signed
  let off := Int64.toInt (mem.imm.interp p)
  BitVec.ofInt 64 (base + off)

@[kstep] def UnscaledAddrExpr.checkSPAlignment (mem : UnscaledAddrExpr) (s : MachineData) (ok : Unit → Effects) : Effects :=
  mem.base.checkSPAlignment s ok

@[kstep] def UnscaledAddrExpr.interpLoad [Labels] {w : Width} (mem : UnscaledAddrExpr) (s : MachineData) (p : Std.Rco Int64) (ret : w.type → MachineData → Effects) :=
  mem.checkSPAlignment s (fun _unit =>
    let addr := mem.eval s p
    MachineData.load s addr w ret)

@[kstep] def UnscaledAddrExpr.interpStore [Labels] {w : Width} (mem : UnscaledAddrExpr) (s : MachineData) (p : Std.Rco Int64)
    (val : w.type) (next : MachineData → Effects) : Effects :=
  mem.checkSPAlignment s (fun _unit =>
    let addr := mem.eval s p
    MachineData.store s addr (w := w) val next)

@[kstep] def Literal.interpLoad [Labels] {w : Width} (expr : Literal) (s : MachineData) (p : Std.Rco Int64) (ret : w.type → MachineData → Effects) : Effects :=
  match expr with
  | .addr addr_expr =>
    let addr_val := Labels.label addr_expr.label
    let addr := BitVec.ofInt 64 (Int64.toInt addr_val)
    MachineData.load s addr w ret
  | .pool litpool_expr =>
    let val := litpool_expr.expr.interp p
    let val_bv : w.type := BitVec.ofInt w.bits (Int64.toInt val)
    ret val_bv s

@[kstep] def AddrOrLit.interpLoad [Labels] {w : Width} (expr : AddrOrLit) (s : MachineData) (p : Std.Rco Int64) (ret : w.type → MachineData → Effects) :=
  match expr with
  | .addr addr_expr => addr_expr.interpLoad s p ret
  | .lit lit_expr => lit_expr.interpLoad s p ret

@[kstep, simp] def maskOfLen {w : RegWidth} (len : Nat) : w.type :=
  if len >= w.bits then
    ~~~(0 : w.type)
  else
    ((1 : w.type) <<< len) - 1

@[kstep, simp] def evalUBFM {w : RegWidth} (src : w.type) (immr imms : Nat) : w.type :=
  if imms % w.bits >= immr % w.bits then
    ((src >>> (immr % w.bits)).take (imms % w.bits - immr % w.bits + 1)).zeroExtend w.bits
  else
    ((src.take (imms % w.bits + 1)).zeroExtend w.bits) <<< (w.bits - immr % w.bits)

@[kstep, simp] def evalSBFM {w : RegWidth} (src : w.type) (immr imms : Nat) : w.type :=
  if imms % w.bits >= immr % w.bits then
    ((src >>> (immr % w.bits)).take (imms % w.bits - immr % w.bits + 1)).signExtend w.bits
  else
    ((src.take (imms % w.bits + 1)).signExtend (w.bits - (w.bits - immr % w.bits))).zeroExtend w.bits <<< (w.bits - immr % w.bits)

@[kstep, simp] def evalBFM {w : RegWidth} (dst src : w.type) (immr imms : Nat) : w.type :=
  if imms % w.bits >= immr % w.bits then
    (dst &&& ~~~(maskOfLen (w := w) (imms % w.bits - immr % w.bits + 1))) |||
      ((src >>> (immr % w.bits)) &&& maskOfLen (w := w) (imms % w.bits - immr % w.bits + 1))
  else
    (dst &&& ~~~((maskOfLen (w := w) (imms % w.bits + 1)) <<< (w.bits - immr % w.bits))) |||
      ((src &&& maskOfLen (w := w) (imms % w.bits + 1)) <<< (w.bits - immr % w.bits))

/-! ### Instruction and Directive Semantics -/

set_option maxHeartbeats 1000000
@[kstep] def Operation.interp [Labels]
  {w} (i : Operation w) (p : Std.Rco Int64) (s : MachineData)
  (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects) : Effects :=
  match (generalizing := false) (motive := Operation w → Effects) i with
  | .LDR dst src => src.interpLoad s p (fun val s => s.setRegOrZr dst val next)
  | .STR src dst => dst.interpStore s p (s.regs.getRegOrZr src) next
  | .LDUR dst src => src.interpLoad s p (fun val s => s.setRegOrZr dst val next)
  | .STUR src dst => dst.interpStore s p (s.regs.getRegOrZr src) next
  -- Memory access ordering of LDP/STP is modeled sequentially (lower address first).
  | .LDP dst1 dst2 src =>
    src.checkSPAlignment s (fun _unit =>
      let (addr, s') := src.eval s p
      MachineData.load s' addr w (fun val1 s'' =>
        MachineData.load s'' (addr + w.bytesv) w (fun val2 s''' =>
          s'''.setRegOrZr dst1 val1 (fun s'''' =>
            s''''.setRegOrZr dst2 val2 next))))
  | .STP src1 src2 dst =>
    dst.checkSPAlignment s (fun _unit =>
      let val1 := s.regs.getRegOrZr src1
      let val2 := s.regs.getRegOrZr src2
      let (addr, s') := dst.eval s p
      MachineData.store s' addr val1 (fun s'' =>
        MachineData.store s'' (addr + w.bytesv) val2 next))
  | .LDRB dst src =>
    src.interpLoad (w := .W8) s p (fun val s' =>
      s'.setRegOrZr dst (val.zeroExtend RegWidth.W32.bits) next)
  | .LDURB dst src =>
    src.interpLoad (w := .W8) s p (fun val s' =>
      s'.setRegOrZr dst (val.zeroExtend RegWidth.W32.bits) next)
  | .STRB src dst =>
    dst.interpStore (w := .W8) s p ((s.regs.getRegOrZr src).take Width.W8.bits) next
  | .STURB src dst =>
    dst.interpStore (w := .W8) s p ((s.regs.getRegOrZr src).take Width.W8.bits) next
  | .LDRSB dst src =>
    src.interpLoad (w := .W8) s p (fun val s' =>
      s'.setRegOrZr dst (val.signExtend w.bits) next)
  | .LDURSB dst src =>
    src.interpLoad (w := .W8) s p (fun val s' =>
      s'.setRegOrZr dst (val.signExtend w.bits) next)
  | .LDRH dst src =>
    src.interpLoad (w := .W16) s p (fun val s' =>
      s'.setRegOrZr dst (val.zeroExtend RegWidth.W32.bits) next)
  | .LDURH dst src =>
    src.interpLoad (w := .W16) s p (fun val s' =>
      s'.setRegOrZr dst (val.zeroExtend RegWidth.W32.bits) next)
  | .STRH src dst =>
    dst.interpStore (w := .W16) s p ((s.regs.getRegOrZr src).take Width.W16.bits) next
  | .STURH src dst =>
    dst.interpStore (w := .W16) s p ((s.regs.getRegOrZr src).take Width.W16.bits) next
  | .LDRSH dst src =>
    src.interpLoad (w := .W16) s p (fun val s' =>
      s'.setRegOrZr dst (val.signExtend w.bits) next)
  | .LDURSH dst src =>
    src.interpLoad (w := .W16) s p (fun val s' =>
      s'.setRegOrZr dst (val.signExtend w.bits) next)
  | .LDRSW dst src =>
    src.interpLoad (w := .W32) s p (fun val s' =>
      s'.setRegOrZr dst (val.signExtend RegWidth.W64.bits) next)
  | .LDURSW dst src =>
    src.interpLoad (w := .W32) s p (fun val s' =>
      s'.setRegOrZr dst (val.signExtend RegWidth.W64.bits) next)
  | .LDPSW dst1 dst2 src =>
    src.checkSPAlignment s (fun _unit =>
      let (addr, s') := src.eval s p
      MachineData.load s' addr .W32 (fun val1 s'' =>
        MachineData.load s'' (addr + Width.W32.bytesv) .W32 (fun val2 s''' =>
          s'''.setRegOrZr dst1 (val1.signExtend RegWidth.W64.bits) (fun s'''' =>
            s''''.setRegOrZr dst2 (val2.signExtend RegWidth.W64.bits) next))))
  | .ADD_e dst src1 src2 =>
    let val1 := s.regs.getRegOrSp src1
    let val2 := src2.interp s.regs p
    let res := val1 + val2
    s.setRegOrSp dst res next
  | .ADD_s dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := src2.interp s.regs p
    let res := val1 + val2
    s.setRegOrZr dst res next
  | .ADDS_e dst src1 src2 =>
    let val1 := s.regs.getRegOrSp src1
    let val2 := src2.interp s.regs p
    let res := val1 + val2
    { s with status := StatusFlags.adds val1 val2 }.setRegOrZr dst res next
  | .ADDS_s dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := src2.interp s.regs p
    let res := val1 + val2
    { s with status := StatusFlags.adds val1 val2 }.setRegOrZr dst res next
  | .SUB_e dst src1 src2 =>
    let val1 := s.regs.getRegOrSp src1
    let val2 := src2.interp s.regs p
    let res := val1 - val2
    s.setRegOrSp dst res next
  | .SUB_s dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := src2.interp s.regs p
    let res := val1 - val2
    s.setRegOrZr dst res next
  | .SUBS_e dst src1 src2 =>
    let val1 := s.regs.getRegOrSp src1
    let val2 := src2.interp s.regs p
    let res := val1 - val2
    { s with status := StatusFlags.subs val1 val2 }.setRegOrZr dst res next
  | .SUBS_s dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := src2.interp s.regs p
    let res := val1 - val2
    { s with status := StatusFlags.subs val1 val2 }.setRegOrZr dst res next
  | .ADC dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let carry : w.type := s.status.c
    let res := val1 + val2 + carry
    s.setRegOrZr dst res next
  | .ADCS dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let carry : w.type := s.status.c
    let res := val1 + val2 + carry
    { s with status := StatusFlags.adcs val1 val2 s.status.c }.setRegOrZr dst res next
  | .SBC dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let borrow : w.type := !s.status.c
    let res := val1 - val2 - borrow
    s.setRegOrZr dst res next
  | .SBCS dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let borrow : w.type := !s.status.c
    let res := val1 - val2 - borrow
    { s with status := StatusFlags.sbcs val1 val2 s.status.c }.setRegOrZr dst res next
  | .MADD dst src1 src2 src3 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let val3 := s.regs.getRegOrZr src3
    let res := val1 * val2 + val3
    s.setRegOrZr dst res next
  | .MSUB dst src1 src2 src3 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let val3 := s.regs.getRegOrZr src3
    let res := val3 - val1 * val2
    s.setRegOrZr dst res next
  | .SMULH dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let prod := val1.signed * val2.signed
    let res := (BitVec.ofInt (RegWidth.W64.bits + RegWidth.W64.bits) prod).extractLsb' RegWidth.W64.bits RegWidth.W64.bits
    s.setRegOrZr dst res next
  | .UMULH dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let prod := val1.unsigned * val2.unsigned
    let res := (BitVec.ofInt (RegWidth.W64.bits + RegWidth.W64.bits) prod).extractLsb' RegWidth.W64.bits RegWidth.W64.bits
    s.setRegOrZr dst res next
  | .SDIV dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    require_const_time [val1.setWidth 64, val2.setWidth 64] (fun _unit =>
      let res := if val2 == 0 then (0 : w.type) else val1.sdiv val2
      s.setRegOrZr dst res next)
  | .UDIV dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    require_const_time [val1.setWidth 64, val2.setWidth 64] (fun _unit =>
      let res := if val2 == 0 then (0 : w.type) else val1 / val2
      s.setRegOrZr dst res next)
  | .SMADDL dst src1 src2 src3 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let val3 := s.regs.getRegOrZr src3
    let res := BitVec.ofInt RegWidth.W64.bits (val1.signed * val2.signed + val3.signed)
    s.setRegOrZr dst res next
  | .UMADDL dst src1 src2 src3 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let val3 := s.regs.getRegOrZr src3
    let res := BitVec.ofInt RegWidth.W64.bits (val1.unsigned * val2.unsigned + val3.unsigned)
    s.setRegOrZr dst res next
  | .SMSUBL dst src1 src2 src3 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let val3 := s.regs.getRegOrZr src3
    let res := BitVec.ofInt RegWidth.W64.bits (val3.signed - val1.signed * val2.signed)
    s.setRegOrZr dst res next
  | .UMSUBL dst src1 src2 src3 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let val3 := s.regs.getRegOrZr src3
    let res := BitVec.ofInt RegWidth.W64.bits (val3.unsigned - val1.unsigned * val2.unsigned)
    s.setRegOrZr dst res next
  | .AND_i dst src1 imm =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := BitVec.ofInt w.bits (Int64.toInt (imm.interp p))
    let res := val1 &&& val2
    s.setRegOrSp dst res next
  | .AND_s dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := src2.interp s.regs p
    let res := val1 &&& val2
    s.setRegOrZr dst res next
  | .ANDS_i dst src1 imm =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := BitVec.ofInt w.bits (Int64.toInt (imm.interp p))
    let res := val1 &&& val2
    { s with status := StatusFlags.logical res }.setRegOrZr dst res next
  | .ANDS_s dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := src2.interp s.regs p
    let res := val1 &&& val2
    { s with status := StatusFlags.logical res }.setRegOrZr dst res next
  | .ORR_i dst src1 imm =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := BitVec.ofInt w.bits (Int64.toInt (imm.interp p))
    let res := val1 ||| val2
    s.setRegOrSp dst res next
  | .ORR_s dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := src2.interp s.regs p
    let res := val1 ||| val2
    s.setRegOrZr dst res next
  | .ORN_s dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := src2.interp s.regs p
    let res := val1 ||| ~~~val2
    s.setRegOrZr dst res next
  | .EOR_i dst src1 imm =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := BitVec.ofInt w.bits (Int64.toInt (imm.interp p))
    let res := val1 ^^^ val2
    s.setRegOrSp dst res next
  | .EOR_s dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := src2.interp s.regs p
    let res := val1 ^^^ val2
    s.setRegOrZr dst res next
  | .BIC_s dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := src2.interp s.regs p
    let res := val1 &&& ~~~val2
    s.setRegOrZr dst res next
  | .EON_s dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := src2.interp s.regs p
    let res := val1 ^^^ ~~~val2
    s.setRegOrZr dst res next
  | .BICS_s dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := src2.interp s.regs p
    let res := val1 &&& ~~~val2
    { s with status := StatusFlags.logical res }.setRegOrZr dst res next
  | .BFM dst src immr imms =>
    let val_dst := s.regs.getRegOrZr dst
    let val_src := s.regs.getRegOrZr src
    let res := evalBFM val_dst val_src immr imms
    s.setRegOrZr dst res next
  | .SBFM dst src immr imms =>
    let val_src := s.regs.getRegOrZr src
    let res := evalSBFM val_src immr imms
    s.setRegOrZr dst res next
  | .UBFM dst src immr imms =>
    let val_src := s.regs.getRegOrZr src
    let res := evalUBFM val_src immr imms
    s.setRegOrZr dst res next
  | .CLZ dst src =>
    let val := s.regs.getRegOrZr src
    s.setRegOrZr dst val.clz next
  | .CLS dst src =>
    let val := s.regs.getRegOrZr src
    let res := (if val.msb then (~~~val).clz else val.clz) - 1#w.bits
    s.setRegOrZr dst res next
  | .RBIT dst src =>
    let val := s.regs.getRegOrZr src
    s.setRegOrZr dst val.reverse next
  | .REV dst src =>
    let val := s.regs.getRegOrZr src
    let res : w.type := match w, val with
      | .W32, v =>
        let step1 := ((v &&& 0x00FF00FF#32) <<< 8) ||| ((v &&& 0xFF00FF00#32) >>> 8)
        ((step1 &&& 0x0000FFFF#32) <<< 16) ||| ((step1 &&& 0xFFFF0000#32) >>> 16)
      | .W64, v =>
        let step1 := ((v &&& 0x00FF00FF00FF00FF#64) <<< 8) ||| ((v &&& 0xFF00FF00FF00FF00#64) >>> 8)
        let step2 := ((step1 &&& 0x0000FFFF0000FFFF#64) <<< 16) ||| ((step1 &&& 0xFFFF0000FFFF0000#64) >>> 16)
        ((step2 &&& 0x00000000FFFFFFFF#64) <<< 32) ||| ((step2 &&& 0xFFFFFFFF00000000#64) >>> 32)
    s.setRegOrZr dst res next
  | .REV16 dst src =>
    let val := s.regs.getRegOrZr src
    let res := ((val &&& 0x00FF00FF00FF00FF#w.bits) <<< 8) ||| ((val &&& 0xFF00FF00FF00FF00#w.bits) >>> 8)
    s.setRegOrZr dst res next
  | .REV32 dst src =>
    let val := s.regs.getRegOrZr src
    let step1 := ((val &&& 0x00FF00FF00FF00FF#64) <<< 8) ||| ((val &&& 0xFF00FF00FF00FF00#64) >>> 8)
    let res := ((step1 &&& 0x0000FFFF0000FFFF#64) <<< 16) ||| ((step1 &&& 0xFFFF0000FFFF0000#64) >>> 16)
    s.setRegOrZr dst res next
  | .EXTR dst src1 src2 lsb =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let lsb := lsb % w.bits
    let res := if lsb == 0 then val2 else (val1 <<< (w.bits - lsb)) ||| (val2 >>> lsb)
    s.setRegOrZr dst res next
  | .MOVZ dst imm shift =>
    let val16 := (BitVec.ofInt w.bits (Int64.toInt (imm.interp p))) &&& 0xFFFF#w.bits
    let res := val16 <<< shift.toNat
    s.setRegOrZr dst res next
  | .MOVK dst imm shift =>
    let oldVal := s.regs.getRegOrZr dst
    let mask := ~~~(0xFFFF#w.bits <<< shift.toNat)
    let val16 := (BitVec.ofInt w.bits (Int64.toInt (imm.interp p))) &&& 0xFFFF#w.bits
    let res := (oldVal &&& mask) ||| (val16 <<< shift.toNat)
    s.setRegOrZr dst res next
  | .MOVN dst imm shift =>
    let val16 := (BitVec.ofInt w.bits (Int64.toInt (imm.interp p))) &&& 0xFFFF#w.bits
    let res := ~~~(val16 <<< shift.toNat)
    s.setRegOrZr dst res next
  | .LSLV dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let shift := val2.toNat % w.bits
    let res := val1 <<< shift
    s.setRegOrZr dst res next
  | .LSRV dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let shift := val2.toNat % w.bits
    let res := val1.ushiftRight shift
    s.setRegOrZr dst res next
  | .ASRV dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let shift := val2.toNat % w.bits
    let res := val1.sshiftRight shift
    s.setRegOrZr dst res next
  | .RORV dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let shift := val2.toNat % w.bits
    let res := val1.rotateRight shift
    s.setRegOrZr dst res next
  | .CSEL dst src1 src2 cond =>
    let val := if cond.interp s.status then s.regs.getRegOrZr src1 else s.regs.getRegOrZr src2
    s.setRegOrZr dst val next
  | .CSINC dst src1 src2 cond =>
    let val := if cond.interp s.status then s.regs.getRegOrZr src1 else s.regs.getRegOrZr src2 + 1#w.bits
    s.setRegOrZr dst val next
  | .CSINV dst src1 src2 cond =>
    let val := if cond.interp s.status then s.regs.getRegOrZr src1 else ~~~(s.regs.getRegOrZr src2)
    s.setRegOrZr dst val next
  | .CSNEG dst src1 src2 cond =>
    let val := if cond.interp s.status then s.regs.getRegOrZr src1 else -(s.regs.getRegOrZr src2)
    s.setRegOrZr dst val next
  | .CCMP_reg src1 src2 nzcv cond =>
    let status' := if cond.interp s.status then
        let val1 := s.regs.getRegOrZr src1
        let val2 := s.regs.getRegOrZr src2
        StatusFlags.subs val1 val2
      else
        StatusFlags.ofNat nzcv
    next { s with status := status' }
  | .CCMP_imm src1 imm nzcv cond =>
    let status' := if cond.interp s.status then
        let val1 := s.regs.getRegOrZr src1
        let val2 := BitVec.ofNat w.bits imm
        StatusFlags.subs val1 val2
      else
        StatusFlags.ofNat nzcv
    next { s with status := status' }
  | .CCMN_reg src1 src2 nzcv cond =>
    let status' := if cond.interp s.status then
        let val1 := s.regs.getRegOrZr src1
        let val2 := s.regs.getRegOrZr src2
        StatusFlags.adds val1 val2
      else
        StatusFlags.ofNat nzcv
    next { s with status := status' }
  | .CCMN_imm src1 imm nzcv cond =>
    let status' := if cond.interp s.status then
        let val1 := s.regs.getRegOrZr src1
        let val2 := BitVec.ofNat w.bits imm
        StatusFlags.adds val1 val2
      else
        StatusFlags.ofNat nzcv
    next { s with status := status' }
  | .ADR dst target =>
    let val := match target with
      | .int64 imm => BitVec.ofInt 64 (Int64.toInt p.lower + Int64.toInt imm)
      | _ => BitVec.ofInt 64 (Int64.toInt (target.interp p))
    s.setRegOrZr dst val next
  | .ADRP dst target =>
    let val := match target with
      | .int64 imm => BitVec.ofInt 64 (Int64.toInt p.lower + Int64.toInt imm)
      | _ => BitVec.ofInt 64 (Int64.toInt (target.interp p))
    s.setRegOrZr dst (val &&& ~~~0xFFF#64) next
  | .B target =>
    jmp (target.evalBranchTarget p) s
  | .B_cond cond target =>
    if cond.interp s.status then
      jmp (target.evalBranchTarget p) s
    else
      next s
  | .BL target =>
    let lr_val := BitVec.ofInt 64 (Int64.toInt p.upper)
    s.setRegOrZr RegOrZr.X30 lr_val (fun s' => jmp (target.evalBranchTarget p) s')
  | .BLR target =>
    let lr_val := BitVec.ofInt 64 (Int64.toInt p.upper)
    let target_val := Int64.ofInt (s.regs.getRegOrZr target).signed
    s.setRegOrZr RegOrZr.X30 lr_val (fun s' => jmp target_val s')
  | .BR target =>
    let target_val := Int64.ofInt (s.regs.getRegOrZr target).signed
    jmp target_val s
  | .RET target =>
    let target_val := Int64.ofInt (s.regs.getRegOrZr target).signed
    jmp target_val s
  | .CBZ reg target =>
    let val := s.regs.getRegOrZr reg
    if val == 0 then
      jmp (target.evalBranchTarget p) s
    else
      next s
  | .CBNZ reg target =>
    let val := s.regs.getRegOrZr reg
    if val != 0 then
      jmp (target.evalBranchTarget p) s
    else
      next s
  | .TBZ reg bit target =>
    let val := s.regs.getRegOrZr reg
    if val.getLsbD bit == false then
      jmp (target.evalBranchTarget p) s
    else
      next s
  | .TBNZ reg bit target =>
    let val := s.regs.getRegOrZr reg
    if val.getLsbD bit == true then
      jmp (target.evalBranchTarget p) s
    else
      next s
  | .NOP => next s

@[kstep] def Instr.interp [Labels]
  (i : Instr) (s : MachineData) (p : Std.Rco Int64)
  (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects) : Effects :=
  require_exec_access p (fun _unit =>
    Operation.interp (w := i.operation_size) i.operation p s next jmp)

@[kstep] def Directive.interp [Labels]
  (d : Directive) (s : MachineData) (p : Std.Rco Int64)
  (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects) : Effects :=
  match d with
  | .label _ => next s
  | .instr i => i.interp s p next jmp
  | .byteArray _ => .unimplemented s!"Unimplemented: execution reached data block at {p.1}"
  | .word _ _ => .unimplemented s!"Unimplemented: execution reached data word at {p.1}"

@[reducible]
instance : ArchDirective Directive MachineData where
  label?
    | .label l => some l
    | _ => none
  interp d s p := Directive.interp d s p .next (fun a s' => .done ⟨s', a⟩)
  undefSeed s := hash s.regs

abbrev Layout := Kraken.Layout Instr ConstExpr

def Directive.fakeSize (d : Directive) : Nat :=
  match d with
  | .instr _ => 4
  | .label _ => 0
  | .byteArray bs => bs.size
  | .word bytes _ => bytes

def Program.fakeLayout (prog : Program) : Executable :=
  let : Inhabited Directive := .mk (.byteArray (.mk #[]))
  let h := hash prog
  let layout : Layout := { start := h.toInt64 <<< 16, size i := prog[i]!.fakeSize }
  layout prog

/-! ### Flag Projections and Carry-Chain Lemmas

Projection lemmas of the flag functions (`@[kcond]`, used when deciding branch conditions) and
limb identities for carry chains. Compare idioms (`subs`/`cmp` followed by a condition code) are
covered by `BitVec.cmp_*` in `Kraken.BitVecArith`. -/

namespace StatusFlags
section
variable {w : Nat} (a b : BitVec w) (cin : Bool)

/-! #### Projections -/

@[simp, kcond, grind =] theorem logical_n (res : BitVec w) : (logical res).n = res.msb := rfl
@[simp, kcond, grind =] theorem logical_z (res : BitVec w) : (logical res).z = decide (res = 0#w) := by
  simp [logical, from_result, Bool.beq_eq_decide_eq]
@[simp, kcond, grind =] theorem logical_c (res : BitVec w) : (logical res).c = false := rfl
@[simp, kcond, grind =] theorem logical_v (res : BitVec w) : (logical res).v = false := rfl

@[simp, kcond, grind =] theorem adds_n : (adds a b).n = (a + b).msb := rfl
@[simp, kcond, grind =] theorem adds_z : (adds a b).z = decide (a + b = 0#w) := by
  simp [adds, from_result, Bool.beq_eq_decide_eq]
@[simp, kcond, grind =] theorem adds_c : (adds a b).c = decide (2 ^ w ≤ a.toNat + b.toNat) :=
  BitVec.unsigned_add_bne a b
@[simp, kcond, grind =] theorem adds_v : (adds a b).v = BitVec.saddOverflow a b :=
  BitVec.signed_add_bne a b

@[simp, kcond, grind =] theorem adcs_n :
    (adcs a b cin).n = (a + b + BitVec.ofNat w cin.toNat).msb := rfl
@[simp, kcond, grind =] theorem adcs_z :
    (adcs a b cin).z = decide (a + b + BitVec.ofNat w cin.toNat = 0#w) := by
  simp [adcs, from_result, Bool.beq_eq_decide_eq]
@[simp, kcond, grind =] theorem adcs_c :
    (adcs a b cin).c = decide (2 ^ w ≤ a.toNat + b.toNat + cin.toNat) :=
  BitVec.unsigned_adc_bne a b cin
@[simp, kcond, grind =] theorem adcs_v (hw : 1 < w) :
    (adcs a b cin).v = decide (a.toInt + b.toInt + cin.toNat < -2 ^ (w - 1) ∨
      2 ^ (w - 1) ≤ a.toInt + b.toInt + cin.toNat) :=
  BitVec.signed_adc_bne a b cin hw

@[simp, kcond, grind =] theorem subs_n : (subs a b).n = (a - b).msb := rfl
@[simp, kcond, grind =] theorem subs_z : (subs a b).z = decide (a = b) := by
  have : a - b = 0#w ↔ a = b := by grind
  simp [subs, from_result, Bool.beq_eq_decide_eq, this]
@[simp, kcond, grind =] theorem subs_c : (subs a b).c = decide (b.toNat ≤ a.toNat) :=
  BitVec.unsigned_sub_beq a b
@[simp, kcond, grind =] theorem subs_v : (subs a b).v = BitVec.ssubOverflow a b :=
  BitVec.signed_sub_bne a b

@[simp, kcond, grind =] theorem sbcs_n :
    (sbcs a b cin).n = (a - b - BitVec.ofNat w (!cin).toNat).msb := rfl
@[simp, kcond, grind =] theorem sbcs_z :
    (sbcs a b cin).z = decide (a - b - BitVec.ofNat w (!cin).toNat = 0#w) := by
  simp [sbcs, from_result, Bool.beq_eq_decide_eq]
@[simp, kcond, grind =] theorem sbcs_c :
    (sbcs a b cin).c = decide (b.toNat + (!cin).toNat ≤ a.toNat) :=
  BitVec.unsigned_sbc_beq a b cin
@[simp, kcond, grind =] theorem sbcs_v (hw : 1 < w) :
    (sbcs a b cin).v = decide (a.toInt - b.toInt - (!cin).toNat < -2 ^ (w - 1) ∨
      2 ^ (w - 1) ≤ a.toInt - b.toInt - (!cin).toNat) :=
  BitVec.signed_sbc_bne a b cin hw

/-! #### Carry-Chain Limb Identities -/

theorem adds_toNat :
    ((a + b).toNat : Int) + ((adds a b).c).toNat * (2 ^ w : Nat) = a.toNat + b.toNat := by
  rw [adds_c]
  exact BitVec.toNat_add_carry a b

theorem adcs_toNat (hw : 0 < w) :
    ((a + b + BitVec.ofNat w cin.toNat).toNat : Int) + ((adcs a b cin).c).toNat * (2 ^ w : Nat) =
      a.toNat + b.toNat + cin.toNat := by
  rw [adcs_c]
  exact BitVec.toNat_adc_carry a b cin hw

theorem subs_toNat :
    ((a - b).toNat : Int) - (!(subs a b).c).toNat * (2 ^ w : Nat) = a.toNat - b.toNat := by
  rw [subs_c]
  exact BitVec.toNat_subs_carry a b

theorem sbcs_toNat (hw : 0 < w) :
    ((a - b - BitVec.ofNat w (!cin).toNat).toNat : Int) - (!(sbcs a b cin).c).toNat * (2 ^ w : Nat) =
      a.toNat - b.toNat - (!cin).toNat := by
  rw [sbcs_c]
  exact BitVec.toNat_sbcs_carry a b cin hw

end
end StatusFlags

/-! ### 64-bit Word and Byte-Limb Carry/Borrow Helpers

Aliases for the flag functions on `UInt64` and 8-byte little-endian limbs, together with their
single-limb carry/borrow step equations. -/

abbrev sub0Word (b a : UInt64) : BitVec 64 := b.toBitVec - a.toBitVec
abbrev sub0Carry (b a : UInt64) : Bool := (StatusFlags.subs b.toBitVec a.toBitVec).c

abbrev sbcWord (b a : UInt64) (c : Bool) : BitVec 64 :=
  b.toBitVec - a.toBitVec - BitVec.ofNat 64 (!c).toNat
abbrev sbcCarry (b a : UInt64) (c : Bool) : Bool := (StatusFlags.sbcs b.toBitVec a.toBitVec c).c

abbrev add0Word (x y : UInt64) : BitVec 64 := x.toBitVec + y.toBitVec
abbrev add0Carry (x y : UInt64) : Bool := (StatusFlags.adds x.toBitVec y.toBitVec).c

abbrev adcWord (x y : UInt64) (c : Bool) : BitVec 64 :=
  x.toBitVec + y.toBitVec + BitVec.ofNat 64 c.toNat
abbrev adcCarry (x y : UInt64) (c : Bool) : Bool := (StatusFlags.adcs x.toBitVec y.toBitVec c).c

theorem sub0_step (b a : UInt64) :
    ((UInt64.ofBitVec (sub0Word b a)).toNat : Int) - (if sub0Carry b a then 0 else 1) * 256 ^ 8 =
      (b.toNat : Int) - (a.toNat : Int) := by
  have h := StatusFlags.subs_toNat b.toBitVec a.toBitVec
  dsimp only [sub0Word, sub0Carry]
  rw [UInt64.toNat_ofBitVec]
  rcases Bool.eq_false_or_eq_true (StatusFlags.subs b.toBitVec a.toBitVec).c with hc | hc <;>
    simp only [hc, UInt64.toNat_toBitVec, Bool.not_true, Bool.not_false, Bool.toNat_true,
      Bool.toNat_false, Bool.false_eq_true, ↓reduceIte] at h ⊢ <;> omega

theorem sbc_step (b a : UInt64) (c : Bool) :
    ((UInt64.ofBitVec (sbcWord b a c)).toNat : Int) - (if sbcCarry b a c then 0 else 1) * 256 ^ 8 =
      (b.toNat : Int) - (a.toNat : Int) - (if c then 0 else 1) := by
  have h := StatusFlags.sbcs_toNat b.toBitVec a.toBitVec c (by decide)
  dsimp only [sbcWord, sbcCarry]
  rw [UInt64.toNat_ofBitVec]
  rcases Bool.eq_false_or_eq_true (StatusFlags.sbcs b.toBitVec a.toBitVec c).c with hc | hc <;>
    cases c <;>
    simp only [hc, UInt64.toNat_toBitVec, Bool.not_true, Bool.not_false, Bool.toNat_true,
      Bool.toNat_false, Bool.false_eq_true, ↓reduceIte] at h ⊢ <;> omega

theorem add0_step (x y : UInt64) :
    ((UInt64.ofBitVec (add0Word x y)).toNat : Int) + (if add0Carry x y then 1 else 0) * 256 ^ 8 =
      (x.toNat : Int) + (y.toNat : Int) := by
  have h := StatusFlags.adds_toNat x.toBitVec y.toBitVec
  dsimp only [add0Word, add0Carry]
  rw [UInt64.toNat_ofBitVec]
  rcases Bool.eq_false_or_eq_true (StatusFlags.adds x.toBitVec y.toBitVec).c with hc | hc <;>
    simp only [hc, UInt64.toNat_toBitVec, Bool.toNat_true, Bool.toNat_false, Bool.false_eq_true,
      ↓reduceIte] at h ⊢ <;> omega

theorem adc_step (x y : UInt64) (c : Bool) :
    ((UInt64.ofBitVec (adcWord x y c)).toNat : Int) + (if adcCarry x y c then 1 else 0) * 256 ^ 8 =
      (x.toNat : Int) + (y.toNat : Int) + (if c then 1 else 0) := by
  have h := StatusFlags.adcs_toNat x.toBitVec y.toBitVec c (by decide)
  dsimp only [adcWord, adcCarry]
  rw [UInt64.toNat_ofBitVec]
  rcases Bool.eq_false_or_eq_true (StatusFlags.adcs x.toBitVec y.toBitVec c).c with hc | hc <;>
    cases c <;>
    simp only [hc, UInt64.toNat_toBitVec, Bool.toNat_true, Bool.toNat_false, Bool.false_eq_true,
      ↓reduceIte] at h ⊢ <;> omega

namespace Kraken.AArch64

abbrev adcsWord (a_bs b_bs : List UInt8) (c : Bool) : BitVec 64 :=
  BitVec.ofInt 64 (Int.ofBytes a_bs) +
  BitVec.ofInt 64 (Int.ofBytes b_bs) +
  BitVec.ofNat 64 c.toNat

/-- The carry flag after `adcs` on two 8-byte little-endian limbs. -/
abbrev adcsCarry (a_bs b_bs : List UInt8) (c : Bool) : Bool :=
  (StatusFlags.adcs (BitVec.ofInt 64 (Int.ofBytes a_bs)) (BitVec.ofInt 64 (Int.ofBytes b_bs)) c).c

theorem adcs_step_bytes (a_bs b_bs : List UInt8) (c : Bool)
    (ha : a_bs.length = 8) (hb : b_bs.length = 8) :
    Int.ofBytes (Int.toBytes 8 (adcsWord a_bs b_bs c).toInt) +
      (if adcsCarry a_bs b_bs c then 1 else 0) * 256 ^ 8 =
      Int.ofBytes a_bs + Int.ofBytes b_bs + (if c then 1 else 0) := by
  have h := StatusFlags.adcs_toNat (BitVec.ofInt 64 (Int.ofBytes a_bs))
    (BitVec.ofInt 64 (Int.ofBytes b_bs)) c (by decide)
  rw [Int.ofBytes_toNat_ofInt_64 a_bs ha, Int.ofBytes_toNat_ofInt_64 b_bs hb] at h
  dsimp only [adcsWord, adcsCarry]
  rw [Int.ofBytes_toBytes_8_toInt]
  rcases Bool.eq_false_or_eq_true (StatusFlags.adcs (BitVec.ofInt 64 (Int.ofBytes a_bs))
    (BitVec.ofInt 64 (Int.ofBytes b_bs)) c).c with hc | hc <;> cases c <;>
    simp only [hc, Bool.toNat_true, Bool.toNat_false, Bool.false_eq_true, ↓reduceIte,
      Int.natCast_zero, Int.natCast_one] at h ⊢ <;> omega

abbrev sbcsWord (a_bs b_bs : List UInt8) (c : Bool) : BitVec 64 :=
  BitVec.ofInt 64 (Int.ofBytes a_bs) -
  BitVec.ofInt 64 (Int.ofBytes b_bs) -
  BitVec.ofNat 64 (!c).toNat

/-- The carry flag after `sbcs` on two 8-byte little-endian limbs. -/
abbrev sbcsCarry (a_bs b_bs : List UInt8) (c : Bool) : Bool :=
  (StatusFlags.sbcs (BitVec.ofInt 64 (Int.ofBytes a_bs)) (BitVec.ofInt 64 (Int.ofBytes b_bs)) c).c

theorem sbcs_step_bytes (a_bs b_bs : List UInt8) (c : Bool)
    (ha : a_bs.length = 8) (hb : b_bs.length = 8) :
    Int.ofBytes (Int.toBytes 8 (sbcsWord a_bs b_bs c).toInt) -
      (if sbcsCarry a_bs b_bs c then 0 else 1) * 256 ^ 8 =
      Int.ofBytes a_bs - Int.ofBytes b_bs - (if c then 0 else 1) := by
  have h := StatusFlags.sbcs_toNat (BitVec.ofInt 64 (Int.ofBytes a_bs))
    (BitVec.ofInt 64 (Int.ofBytes b_bs)) c (by decide)
  rw [Int.ofBytes_toNat_ofInt_64 a_bs ha, Int.ofBytes_toNat_ofInt_64 b_bs hb] at h
  dsimp only [sbcsWord, sbcsCarry]
  rw [Int.ofBytes_toBytes_8_toInt]
  rcases Bool.eq_false_or_eq_true (StatusFlags.sbcs (BitVec.ofInt 64 (Int.ofBytes a_bs))
    (BitVec.ofInt 64 (Int.ofBytes b_bs)) c).c with hc | hc <;> cases c <;>
    simp only [hc, Bool.not_true, Bool.not_false, Bool.toNat_true, Bool.toNat_false,
      Bool.false_eq_true, ↓reduceIte, Int.natCast_zero, Int.natCast_one] at h ⊢ <;> omega

end Kraken.AArch64


