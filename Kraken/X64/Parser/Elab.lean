module

public import Kraken.X64.Parser.Basic
public meta import Kraken.X64.Parser.Basic
public import Kraken.X64.Parser.Syntax
public meta import Kraken.X64.Parser.Syntax
public import Qq
public meta import Qq
public meta import Lean

/-!
Operands may contain antiquotations (`%❰t❱`), whose value is only known as a term, so everything from
operands upwards is elaborated to `Qq` quoted expressions (`Q(...)`). The widths of an instruction are kept
in the `X64ElabM` state rather than threaded through the operand elaborators: a register reports its width,
which must agree with what the mnemonic suffix and the other operands determined; immediates and memory
operands are valid at any width and simply use the instruction's.
-/

namespace Kraken.X64.Parser

open Lean Meta Elab Term Qq Kraken.Parser

public meta section

-- ============================================================================
-- Elaboration Monad: Operation & Address Widths
-- ============================================================================

structure X64ElabM.State where
  /-- The general-purpose operation width of the instruction (or operand scope) being elaborated:
      a metavariable until the mnemonic suffix or an operand determines it. -/
  operandWidth : Q(Width)
  /-- The AVX vector operation width of the instruction being elaborated: a metavariable until
      an operand determines it. -/
  avxOperandWidth : Q(AvxWidth)
  /-- The address width of the instruction's memory operand, if any. -/
  addressWidth? : Option Q(Width) := none

abbrev X64ElabM := StateRefT X64ElabM.State TermElabM

/-- Run the elaboration of an instruction, whose operation widths are yet to be determined. -/
def X64ElabM.run {α : Type} (x : X64ElabM α) : TermElabM α := do
  x.run' {
    operandWidth := ← mkFreshExprMVarQ q(Width)
    avxOperandWidth := ← mkFreshExprMVarQ q(AvxWidth)
  }

def ppWidth (wExpr : Expr) : MetaM MessageData := do
  let wExpr ← instantiateMVars wExpr  -- an assigned metavariable is not syntactically `Width.W64`
  if let some wValue := [Width.W8, .W16, .W32, .W64].find? (toExpr · == wExpr) then return m!"{wValue}"
  if let some wValue := [AvxWidth.W128, .W256, .W512].find? (toExpr · == wExpr) then return m!"{wValue}"
  return m!"{wExpr}"

/-- The general-purpose operation width of the current instruction. -/
def getOperandWidth : X64ElabM Q(Width) :=
  return (← get).operandWidth

/-- The AVX vector operation width of the current instruction. -/
def getAvxOperandWidth : X64ElabM Q(AvxWidth) :=
  return (← get).avxOperandWidth

/-- Assert that two width expressions are definitionally equal, returning their `=Q` proof. -/
def assertWidthEq {α : Q(Type)} (w' w : Q($α)) : MetaM (PLift ($w' =Q $w)) := do
  match ← isDefEqQ (u := 1) w' w with
  | .defEq h => return ⟨h⟩
  | .notDefEq => throwError "type error: {← ppWidth w'} != {← ppWidth w}"

/-- Record that the current operand has width `w`, which must agree with the width already determined by
    the mnemonic suffix or the previous operands. -/
def setOperandWidth (w : Q(Width)) : X64ElabM Unit := do
  discard <| assertWidthEq (← getOperandWidth) w

/-- Run `body` with its own operation width, initially `w?`, and return the width it determined. -/
private def withOperandWidth {α : Q(Width) → Type} (w? : Option Width)
    (body : (w : Q(Width)) → X64ElabM (α w)) : X64ElabM ((w : Q(Width)) × α w) := do
  let saved ← getOperandWidth
  let w : Q(Width) ← match w? with
    | some w => pure q($w)
    | none => mkFreshExprMVarQ q(Width)
  modify ({ · with operandWidth := w })
  try
    let res ← body w
    pure ⟨w, res⟩
  finally
    modify ({ · with operandWidth := saved })

/-- Elaborate a memory operand: the widths its registers report make up the address width of the
    instruction, not its operation width. x86 instructions take at most one memory operand. -/
def computingAddrWidth {α : Type} (body : X64ElabM α) : X64ElabM α := do
  let ⟨w, res⟩ ← withOperandWidth none fun _ => body
  if (← get).addressWidth?.isSome then throwError "can't have two memory operands"
  let w ← instantiateMVars w
  modify ({ · with addressWidth? := some w })
  pure res

/-- Elaborate the source operand of an unsuffixed widening move (`movsx`/`movzx`) in its own operation
    width, which must be narrower than the instruction's; checked once both are known. Returns the
    source width. -/
def withFreshOperandWidthUnderCurrent {α : Q(Width) → Type}
    (body : (w : Q(Width)) → X64ElabM (α w)) : X64ElabM ((w : Q(Width)) × α w) := do
  let ⟨wSrc, res⟩ ← withOperandWidth none body
  checkUnder wSrc
  pure ⟨wSrc, res⟩
where
  checkUnder (wSrc : Q(Width)) : X64ElabM Unit := do
    let wSrc ← instantiateMVars wSrc
    let wDst ← instantiateMVars (← getOperandWidth)
    let value? (w : Expr) := [Width.W8, .W16, .W32, .W64].find? (toExpr · == w)
    if let (some s, some d) := (value? wSrc, value? wDst) then
      unless s.bits < d.bits do throwError "source width {s} must be narrower than destination width {d}"

/-- Build `Instr.regular` from the instruction's widths and its operation `op`. The operation width must
    have been determined, unless `ifUndetermined` provides it (`push`/`pop` default to 64 bits). -/
def mkRegularInstr (w : Q(Width)) (op : Q(Operation $w)) (ifUndetermined : Option Width := none) : X64ElabM Q(Instr) := do
  let w' ← instantiateMVars w
  if w'.isMVar then
    let d : Width ← ifUndetermined.getDM <| throwError "could not infer operand width"
    w'.mvarId!.assign q($d)
  let aw := (← get).addressWidth?.getD q(.W64)
  instantiateMVars q(Instr.regular $aw $w $op)

/-- Build `Instr.avx` from the instruction's widths and its AVX operation `op`. -/
def mkAvxInstr (w : Q(AvxWidth)) (op : Q(AvxOperation $w)) : X64ElabM Q(Instr) := do
  let w' ← instantiateMVars w
  if w'.isMVar then throwError "could not infer operand width"
  let aw := (← get).addressWidth?.getD q(.W64)
  instantiateMVars q(Instr.avx $aw $w $op)

/-- Elaborate the term `t` of an antiquotation at the type `ty` expected by its position. Elaboration is
    forced to finish here (`withSynthesize`) because the instruction inspects the result right away: the
    unification of `ty` against `t`'s type is what determines the operation width, and `mkRegularInstr`
    rejects a width that is still a metavariable. A postponed `t` would leave a placeholder of type `ty`
    behind, with the width undetermined. A type mismatch aborts the instruction instead of being recovered
    as `sorry`. -/
def elabAntiquot {ty : Q(Type)} (t : Term) : TermElabM Q($ty) :=
  withoutErrToSorry <| withSynthesize <| elabTermEnsuringTypeQ t ty

-- ============================================================================
-- Constant Expression Evaluation
-- ============================================================================

/-- Evaluate an `x64_const` syntax node into a `ConstExpr`. -/
def evalConstExpr (stx : TSyntax `x64_const) : TermElabM ConstExpr := withRef stx do
  match stx with
  | `(x64_const| +$n:num)
  | `(x64_const| $n:num) =>
    let i ← Int64.ofNatNoOverflow n.getNat
    pure (.int64 i)
  | `(x64_const| -$n:num) =>
    let i ← Int64.ofIntNoOverflow (-(Int.ofNat n.getNat))
    pure (.int64 i)
  | `(x64_const| $id:x64_ident + $n:num) =>
    let s ← getAsmIdent id
    let i ← withRef n <| Int64.ofNatNoOverflow n.getNat
    pure (.add (.label s) (.int64 i))
  | `(x64_const| $id:x64_ident - $n:num) =>
    let s ← getAsmIdent id
    let i ← withRef n <| Int64.ofNatNoOverflow n.getNat
    pure (.sub (.label s) (.int64 i))
  | `(x64_const| $id:x64_ident) =>
    let s ← getAsmIdent id
    pure (.label s)
  | _ => throwError "invalid constant expression"

/-- The constant of an `x64_imm` (`$const`). -/
def getImmConst (stx : TSyntax `x64_imm) : TermElabM (TSyntax `x64_const) := withRef stx do
  match stx with
  | ⟨.node _ _ #[.atom _ "$", c]⟩ => pure ⟨c⟩
  | _ => throwError "invalid immediate operand"

-- ============================================================================
-- Register Evaluation & Elaboration
-- ============================================================================

/-- Evaluate an `x64_reg` syntax node into a general-purpose register and its width. -/
def evalReg (stx : TSyntax `x64_reg) : TermElabM ((w : Width) × Reg w) := withRef stx do
  let `(x64_reg| %$r:x64_reg_name) := stx
    | throwError "expected general-purpose register"
  let (stem, sfx) ← splitSuffixed r
  let legacy64 : String → Option Reg64
    | "ax" | "a" => some .rax | "bx" | "b" => some .rbx
    | "cx" | "c" => some .rcx | "dx" | "d" => some .rdx
    | "si"       => some .rsi | "di"       => some .rdi
    | "sp"       => some .rsp | "bp"       => some .rbp
    | _          => none
  let ext64 : String → Option Reg64
    | "r8"  => some .r8  | "r9"  => some .r9  | "r10" => some .r10 | "r11" => some .r11
    | "r12" => some .r12 | "r13" => some .r13 | "r14" => some .r14 | "r15" => some .r15
    | _     => none
  match stem, sfx with
  -- 64-bit legacy registers (`%rax`..`%rbp`)
  | "r", s =>
    let some reg := legacy64 s | throwError "invalid 64-bit register"
    pure ⟨.W64, .low reg .W64⟩
  -- 32-bit legacy registers (`%eax`..`%ebp`)
  | "e", s =>
    let some reg := legacy64 s | throwError "invalid 32-bit register"
    pure ⟨.W32, .low reg .W32⟩
  -- 8-bit high byte registers (`%ah`, `%bh`, `%ch`, `%dh`)
  | "a", "h" => pure ⟨.W8, .ah⟩
  | "b", "h" => pure ⟨.W8, .bh⟩
  | "c", "h" => pure ⟨.W8, .ch⟩
  | "d", "h" => pure ⟨.W8, .dh⟩
  -- 16-bit accumulator/base/counter/data registers (`%ax`, `%bx`, `%cx`, `%dx`)
  | s, "x" =>
    let some reg := legacy64 s | throwError "invalid 16-bit register"
    pure ⟨.W16, .low reg .W16⟩
  -- 8-bit low legacy registers (`%al`..`%dl`, `%sil`..`%bpl`)
  | s, "l" =>
    let some reg := legacy64 s | throwError "invalid 8-bit register"
    pure ⟨.W8, .low reg .W8⟩
  -- Unsuffixed registers: 64-bit extended (`%r8`..`%r15`) or 16-bit index/pointer (`%si`..`%bp`)
  | s, "" =>
    if let some reg := ext64 s then pure ⟨.W64, .low reg .W64⟩
    else if let some reg := legacy64 s then pure ⟨.W16, .low reg .W16⟩
    else throwError "invalid register"
  -- 32-bit extended registers (`%r8d`..`%r15d`)
  | s, "d" =>
    let some reg := ext64 s | throwError "invalid 32-bit extended register"
    pure ⟨.W32, .low reg .W32⟩
  -- 16-bit extended registers (`%r8w`..`%r15w`)
  | s, "w" =>
    let some reg := ext64 s | throwError "invalid 16-bit extended register"
    pure ⟨.W16, .low reg .W16⟩
  -- 8-bit extended registers (`%r8b`..`%r15b`)
  | s, "b" =>
    let some reg := ext64 s | throwError "invalid 8-bit extended register"
    pure ⟨.W8, .low reg .W8⟩
  | _, _ => throwError "expected general-purpose register"

/-- Elaborate an `x64_reg` into a `Q(Reg $w)`, where `w` is the operation width of the
    instruction: a concrete register determines it, an antiquotation `%❰t❱` is elaborated at it. -/
def elabReg {w : Q(Width)} (stx : TSyntax `x64_reg) : X64ElabM Q(Reg $w) := withRef stx do
  match stx with
  | `(x64_reg| %❰ $t ❱) =>
    elabAntiquot t
  | _ =>
    let ⟨w', reg⟩ ← evalReg stx
    let ⟨_⟩ ← assertWidthEq w q($w')
    pure q($reg)

/-- Evaluate an `x64_avx_reg` syntax node into an AVX vector register and its width. -/
def evalAvxReg (stx : TSyntax `x64_avx_reg) : TermElabM ((w : AvxWidth) × AvxReg w) := withRef stx do
  let `(x64_avx_reg| %$r:x64_avx_reg_name) := stx
    | throwError "expected AVX register"
  let (stem, sfx) ← splitSuffixed r
  let mm ← match sfx with
    | "0"  => pure RegMm.mm0  | "1"  => pure RegMm.mm1  | "2"  => pure RegMm.mm2  | "3"  => pure RegMm.mm3
    | "4"  => pure RegMm.mm4  | "5"  => pure RegMm.mm5  | "6"  => pure RegMm.mm6  | "7"  => pure RegMm.mm7
    | "8"  => pure RegMm.mm8  | "9"  => pure RegMm.mm9  | "10" => pure RegMm.mm10 | "11" => pure RegMm.mm11
    | "12" => pure RegMm.mm12 | "13" => pure RegMm.mm13 | "14" => pure RegMm.mm14 | "15" => pure RegMm.mm15
    | "16" => pure RegMm.mm16 | "17" => pure RegMm.mm17 | "18" => pure RegMm.mm18 | "19" => pure RegMm.mm19
    | "20" => pure RegMm.mm20 | "21" => pure RegMm.mm21 | "22" => pure RegMm.mm22 | "23" => pure RegMm.mm23
    | "24" => pure RegMm.mm24 | "25" => pure RegMm.mm25 | "26" => pure RegMm.mm26 | "27" => pure RegMm.mm27
    | "28" => pure RegMm.mm28 | "29" => pure RegMm.mm29 | "30" => pure RegMm.mm30 | "31" => pure RegMm.mm31
    | _    => throwError "invalid AVX register index '{sfx}'"
  match stem with
  | "xmm" => pure ⟨.W128, .xmm mm⟩
  | "ymm" => pure ⟨.W256, .ymm mm⟩
  | "zmm" => pure ⟨.W512, .zmm mm⟩
  | _     => throwError "invalid AVX register prefix '{stem}'"

/-- Elaborate an `x64_avx_reg` into a `Q(AvxReg $w)`, where `w` is the AVX operation width of the
    instruction. -/
def elabAvxReg {w : Q(AvxWidth)} (stx : TSyntax `x64_avx_reg) : X64ElabM Q(AvxReg $w) := withRef stx do
  match stx with
  | `(x64_avx_reg| %❰ $t ❱) =>
    elabAntiquot t
  | _ =>
    let ⟨w', reg⟩ ← evalAvxReg stx
    let ⟨_⟩ ← assertWidthEq w q($w')
    pure q($reg)

/-- Evaluate a low register for memory addressing (rejecting `%ah`/`%bh`/`%ch`/`%dh`). -/
def evalLowReg (stx : TSyntax `x64_reg) : TermElabM (Width × Reg64) := withRef stx do
  let ⟨w, r⟩ ← evalReg stx
  match r with
  | .low r64 _ => pure (w, r64)
  | _ => throwError "high byte register cannot be used for an addrexpr"

/-- Elaborate a low register for memory addressing into a `Q(Reg64)`, reporting its width
    (the address width, see `computingAddrWidth`); an antiquotation `%❰t❱` is elaborated at `Reg64` and
    denotes a 64-bit address. -/
def elabLowReg (stx : TSyntax `x64_reg) : X64ElabM Q(Reg64) := withRef stx do
  match stx with
  | `(x64_reg| %❰ $t ❱) =>
    setOperandWidth q(.W64)
    elabAntiquot t
  | _ =>
    let (w, r) ← evalLowReg stx
    setOperandWidth q($w)
    pure q($r)

/-- Elaborate a base register for memory addressing (`%rip` or a low GPR) into a `Q(RegOrRip)`. -/
def elabRegOrRip (stx : TSyntax `x64_reg_or_rip) : X64ElabM Q(RegOrRip) := withRef stx do
  match stx with
  | `(x64_reg_or_rip| %rip) =>
    setOperandWidth q(.W64)
    pure q(.rip)
  | `(x64_reg_or_rip| $r:x64_reg) =>
    let r ← elabLowReg r
    return q(.reg $r)
  | _ => throwError "expected memory base register"

-- ============================================================================
-- Memory & General Operand Elaboration
-- ============================================================================

/-- Evaluate a numeric memory index scale (`1`, `2`, `4`, or `8`) into its corresponding `Width`. -/
def evalScale (stx : TSyntax `num) : X64ElabM Width := withRef stx do
  match stx.getNat with
  | 1 => pure .W8
  | 2 => pure .W16
  | 4 => pure .W32
  | 8 => pure .W64
  | s => throwError "invalid scale {s}, must be 1, 2, 4, or 8"

/-- Elaborate an `x64_mem` syntax node into a `Q(AddrExpr)`, recording the instruction's
    address width. -/
def elabMem (stx : TSyntax `x64_mem) : X64ElabM Q(AddrExpr) := withRef stx <| computingAddrWidth do
  match stx with
  | `(x64_mem| $[$disp?:x64_const]?($baseStx:x64_reg_or_rip $[, $idxStx?:x64_reg $[, $scStx??:num]?]?)) =>
    let base ← elabRegOrRip baseStx
    let disp : ConstExpr ← match disp? with
      | some disp =>
        let disp ← evalConstExpr disp
        if base.isConstOf ``RegOrRip.rip && ! disp matches .int64 _ then
          pure <| .sub disp .after_current_instruction
        else pure disp
      | none => pure <| .int64 0
    let scale : Width ← (evalScale <$> scStx??.join).getD (pure .W8)
    let idx? : Q(Option AddrIndex) ← match idxStx? with
      | some idx =>
        let idx ← elabLowReg idx
        pure q(some ⟨$idx, $scale⟩)
      | none => pure q(none)
    return q({ base := some $base, idx := $idx?, disp := $disp })
  | `(x64_mem| $disp:x64_const) =>
    setOperandWidth q(.W64)
    let d : ConstExpr ← evalConstExpr disp
    return q({ base := none, idx := none, disp := $d })
  | _ => throwError "invalid memory operand"

/-- Extract the symbol name of a `$sym` immediate, which Lean parses as an antiquotation node. -/
def getAntiquotSym (stx : Syntax) : TermElabM String := withRef stx do
  unless stx.isAntiquot do throwError "invalid operand"
  let name := stx.getAntiquotTerm.getId
  if name.isAnonymous then throwError "invalid operand"
  pure name.toString

/-- Elaborate an `x64_reg_or_mem` into a `Q(RegOrMem $w)`. -/
def elabRegOrMem {w : Q(Width)} (stx : TSyntax `x64_reg_or_mem) : X64ElabM Q(RegOrMem $w) := withRef stx do
  match stx with
  | `(x64_reg_or_mem| $r:x64_reg) =>
    let r ← elabReg r
    return q(.reg $r)
  | `(x64_reg_or_mem| $m:x64_mem) =>
    let m ← elabMem m
    return q(.mem $m)
  | _ => throwError "expected register or memory operand"

/-- Elaborate an `x64_operand` in a position that admits no immediate (a destination) into a
    `Q(RegOrMem $w)`. -/
def elabRegOrMemOperand {w : Q(Width)} (stx : TSyntax `x64_operand) : X64ElabM Q(RegOrMem $w) := withRef stx do
  match stx with
  | `(x64_operand| $rm:x64_reg_or_mem) => elabRegOrMem rm
  | `(x64_operand| ❰ $t ❱) => elabAntiquot t
  | _ => throwError "expected register or memory operand, got $"

/-- Elaborate an `x64_operand` into a `Q(Operand $w)`. -/
def elabOperand {w : Q(Width)} (stx : TSyntax `x64_operand) : X64ElabM Q(Operand $w) := withRef stx do
  if stx.raw.isAntiquot then
    let sym : String ← getAntiquotSym stx.raw
    return q(.imm (.label $sym))
  else match stx with
  | `(x64_operand| $rm:x64_reg_or_mem) =>
    let rm ← elabRegOrMem rm
    return q(.regOrMem $rm)
  | `(x64_operand| $i:x64_imm) =>
    let ce : ConstExpr ← evalConstExpr (← getImmConst i)
    return q(.imm $ce)
  | `(x64_operand| ❰ $t ❱) => elabAntiquot t
  -- `$sym ± n`: the left operand is the `$sym` antiquotation node (see the grammar).
  | `(x64_operand| $sym:x64_operand + $n:num) =>
    let s : String ← getAntiquotSym sym.raw
    let i : Int64 ← withRef n <| Int64.ofNatNoOverflow n.getNat
    return q(.imm (.add (.label $s) (.int64 $i)))
  | `(x64_operand| $sym:x64_operand - $n:num) =>
    let s : String ← getAntiquotSym sym.raw
    let i : Int64 ← withRef n <| Int64.ofNatNoOverflow n.getNat
    return q(.imm (.sub (.label $s) (.int64 $i)))
  | _ => throwError "invalid operand"

/-- Elaborate an `x64_avx_operand` into a `Q(AvxRegOrMem $w)`. -/
def elabAvxRegOrMem {w : Q(AvxWidth)} (stx : TSyntax `x64_avx_operand) : X64ElabM Q(AvxRegOrMem $w) := withRef stx do
  match stx with
  | `(x64_avx_operand| $r:x64_avx_reg) =>
    let r ← elabAvxReg r
    return q(.avx $r)
  | `(x64_avx_operand| $m:x64_mem) =>
    let m ← elabMem m
    return q(.mem $m)
  | `(x64_avx_operand| ❰ $t ❱) => elabAntiquot t
  | _ => throwError "expected AVX register or memory operand"

/-- Elaborate a relative branch target (`RelRegOrMem`) from an `x64_operand`. -/
def elabRelTarget (stx : TSyntax `x64_operand) : X64ElabM Q(RelRegOrMem) := withRef stx do
  match stx with
  | `(x64_operand| $r:x64_reg) =>
    let ⟨w, reg⟩ ← withOperandWidth none (elabReg (w := ·) r)
    let .defEq _ ← isDefEqQ (u := 1) w q(.W64)
      | throwError "expected a 64-bit register in relative addressing position"
    pure q(.reg $reg)
  | `(x64_operand| $id:x64_ident) =>
    let lbl : String ← getAsmIdent id
    pure q(.rel (.sub (.label $lbl) .after_current_instruction))
  | `(x64_operand| $_:x64_const) =>
    -- Labels are handled above.
    throwError "absolute branch targets are not supported"
  | `(x64_operand| $m:x64_mem) =>
    let m ← elabMem m
    return q(.mem $m)
  | _ => throwError "invalid branch target operand"

/-- Evaluate an `x64_shift_count` (`$imm` or `%cl`) into a `ShiftCountExpr`. -/
def evalShiftCount (stx : TSyntax `x64_shift_count) : TermElabM ShiftCountExpr := withRef stx do
  if stx.raw.isAntiquot then
    let s ← getAntiquotSym stx.raw
    pure (.imm8 (.label s))
  else match stx with
  | `(x64_shift_count| %cl) => pure .cl
  | `(x64_shift_count| $imm:x64_imm) => return .imm8 (← evalConstExpr (← getImmConst imm))
  | _ => throwError "expected immediate or %cl shift count"

-- ============================================================================
-- Mnemonic Suffixes & Constructors
-- ============================================================================

/-- Evaluate the operand-width suffix of a mnemonic (`""`, `"b"`, `"w"`, `"l"`, `"q"`). -/
def evalWidthSuffix (suffix : String) : TermElabM (Option Width) :=
  match suffix with
  | ""  => return none
  | "b" => return (some .W8)
  | "w" => return (some .W16)
  | "l" => return (some .W32)
  | "q" => return (some .W64)
  | sfx => throwError "invalid operand width suffix '{sfx}'"

/-- Set the instruction's operation width from its mnemonic's width suffix, when present. -/
def setSuffixWidth (stx : Syntax) : X64ElabM Unit := do
  if let some w ← evalWidthSuffix (← getAffixedSuffix stx) then
    setOperandWidth q($w)

/-- Evaluate the condition-code suffix of a mnemonic (`cmov<cc>`, `set<cc>`, `j<cc>`). -/
def evalCondCodeSuffix (stx : Syntax) : TermElabM CondCode := withRef stx do
  match ← getAffixedSuffix stx with
  | "z"  | "e"          => return .z
  | "nz" | "ne"         => return .nz
  | "b"  | "c"  | "nae" => return .b
  | "ae" | "nc" | "nb"  => return .ae
  | "a"  | "nbe"        => return .a
  | "be" | "na"         => return .be
  | "l"  | "nge"        => return .l
  | "le" | "ng"         => return .le
  | sfx                 => throwError "invalid condition code '{sfx}'"

/-- The `Operation` constructor of an `x64_bin_op`. -/
def elabBinOp (stx : TSyntax `x64_bin_op) :
    TermElabM Q({w : Width} → Dst w → Operand w → Operation w) := withRef stx do
  match (← splitSuffixed stx).1 with
  | "add"            => pure q(@Operation.add)
  | "adc"            => pure q(@Operation.adc)
  | "sub"            => pure q(@Operation.sub)
  | "sbb"            => pure q(@Operation.sbb)
  | "mov" | "movabs" => pure q(@Operation.mov)
  | "xor"            => pure q(@Operation.xor)
  | "and"            => pure q(@Operation.and)
  | "or"             => pure q(@Operation.or)
  | "cmp"            => pure q(@Operation.cmp)
  | "test"           => pure q(@Operation.test)
  | stem             => throwError "invalid binary instruction mnemonic '{stem}'"

/-- The `Operation` constructor of an `x64_rm_reg_op`. -/
def elabRmRegOp (stx : TSyntax `x64_rm_reg_op) :
    TermElabM Q({w : Width} → Reg w → RegOrMem w → Operation w) := withRef stx do
  match (← splitSuffixed stx).1 with
  | "adcx" => pure q(@Operation.adcx)
  | "adox" => pure q(@Operation.adox)
  | stem   => throwError "invalid carry-chain mnemonic '{stem}'"

/-- The `Operation` constructor of an `x64_unary_op`. -/
def elabUnaryOp (stx : TSyntax `x64_unary_op) :
    TermElabM Q({w : Width} → RegOrMem w → Operation w) := withRef stx do
  match (← splitSuffixed stx).1 with
  | "mul" => pure q(@Operation.mul)
  | "neg" => pure q(@Operation.neg)
  | "dec" => pure q(@Operation.dec)
  | "inc" => pure q(@Operation.inc)
  | "not" => pure q(@Operation.not)
  | stem  => throwError "invalid unary instruction mnemonic '{stem}'"

/-- The `(srcWidth, dstWidth)` and `Operation` constructor of an `x64_ext_mov_op`. -/
def elabExtMovOp (stx : TSyntax `x64_ext_mov_op) :
    TermElabM (Q({w w' : Width} → Dst w → RegOrMem w' → Operation w) × Width × Width) := withRef stx do
  let (stem, sfx) ← splitSuffixed stx
  let op : Q({w w' : Width} → Dst w → RegOrMem w' → Operation w) ← match stem with
    | "movs" => pure q(@Operation.movsx)
    | "movz" => pure q(@Operation.movzx)
    | _      => throwError "invalid extending move mnemonic '{stem}'"
  let ws ← match sfx with
    | "bw"        => pure (.W8,  .W16)
    | "bl"        => pure (.W8,  .W32)
    | "bq"        => pure (.W8,  .W64)
    | "wl"        => pure (.W16, .W32)
    | "wq"        => pure (.W16, .W64)
    | "lq" | "xd" => pure (.W32, .W64)
    | _           => throwError "invalid extension width suffix '{sfx}'"
  pure (op, ws)

/-- The `AvxOperation` constructor of an `x64_avx_op`. -/
def elabAvxOp (stx : TSyntax `x64_avx_op) :
    TermElabM Q({w : AvxWidth} → AvxDst w → AvxRegOrMem w → AvxOperation w) := withRef stx do
  let (stem, sfx) ← splitSuffixed stx
  match stem, sfx with
  | "movu",  "ps" => pure q(@AvxOperation.movups)
  | "vmovu", "ps" => pure q(@AvxOperation.vmovups)
  | "mova",  "ps" => pure q(@AvxOperation.movaps)
  | "add",   "ps" => pure q(@AvxOperation.addps)
  | "sub",   "ps" => pure q(@AvxOperation.subps)
  | _, _          => throwError "invalid AVX mnemonic"

/-- The `Operation` constructor of an `x64_shift_op`. -/
def elabShiftOp (stx : TSyntax `x64_shift_op) :
    TermElabM Q({w : Width} → Dst w → ShiftCountExpr → Operation w) := withRef stx do
  match (← splitSuffixed stx).1 with
  | "shl" | "sal" => pure q(@Operation.shl)
  | "shr"         => pure q(@Operation.shr)
  | "sar"         => pure q(@Operation.sar)
  | "rol"         => pure q(@Operation.rol)
  | "ror"         => pure q(@Operation.ror)
  | "rcl"         => pure q(@Operation.rcl)
  | "rcr"         => pure q(@Operation.rcr)
  | stem          => throwError "invalid shift/rotate mnemonic '{stem}'"

/-- The `Operation` constructor of an `x64_shd_op`. -/
def elabShdOp (stx : TSyntax `x64_shd_op) :
    TermElabM Q({w : Width} → Dst w → Reg w → ShiftCountExpr → Operation w) := withRef stx do
  match ← getAffixedStem stx with
  | "shld" => pure q(@Operation.shld)
  | "shrd" => pure q(@Operation.shrd)
  | stem   => throwError "invalid double-precision shift mnemonic '{stem}'"

-- ============================================================================
-- Instruction Elaboration
-- ============================================================================

/-- Elaborate an `x64_instr` syntax node into a `Q(Instr)`. Each arm records the mnemonic's width
    suffix before elaborating the operands, so that an operand disagreeing with the suffix is reported
    against the suffix. -/
def elabInstr (stx : TSyntax `x64_instr) : X64ElabM Q(Instr) := withRef stx do
  let w ← getOperandWidth
  match stx with
  | `(x64_instr| ❰ $t ❱) => elabAntiquot t
  | `(x64_instr| .align $align:num $[, $pad?:num]?) =>
    let align : Nat := align.getNat
    let pad? : Option Nat := pad?.map (·.getNat)
    return q(.regular .W64 .W64 (.nopalign $align $pad?))
  | `(x64_instr| $op:x64_bin_op $src:x64_operand, $dst:x64_operand) =>
    let mk ← elabBinOp op
    setSuffixWidth op
    let src ← elabOperand src
    let dst ← elabRegOrMemOperand dst
    mkRegularInstr w q($mk $dst $src)
  | `(x64_instr| $op:x64_rm_reg_op $src:x64_operand, $dst:x64_reg) =>
    let mk ← elabRmRegOp op
    setSuffixWidth op
    let src ← elabRegOrMemOperand src
    let dst ← elabReg dst
    mkRegularInstr w q($mk $dst $src)
  | `(x64_instr| $op:x64_cmov_op $src:x64_operand, $dst:x64_reg) =>
    let cc : CondCode ← evalCondCodeSuffix op
    let src ← elabRegOrMemOperand src
    let dst ← elabReg dst
    mkRegularInstr w q(.cmovcc $cc $dst $src)
  | `(x64_instr| $op:x64_unary_op $dst:x64_operand) =>
    let mk ← elabUnaryOp op
    setSuffixWidth op
    let dst ← elabRegOrMemOperand dst
    mkRegularInstr w q($mk $dst)
  | `(x64_instr| $op:x64_set_op $dst:x64_operand) =>
    let cc : CondCode ← evalCondCodeSuffix op
    setOperandWidth q(.W8)
    let dst ← elabRegOrMemOperand dst
    mkRegularInstr w q(.setcc $cc $dst)
  | `(x64_instr| $op:x64_imul_op $src:x64_operand) =>
    setSuffixWidth op
    let src ← elabRegOrMemOperand src
    mkRegularInstr w q(.imul1 $src)
  | `(x64_instr| $op:x64_imul_op $src:x64_operand, $dst:x64_operand) =>
    setSuffixWidth op
    let src ← elabOperand src
    let dst ← elabRegOrMemOperand dst
    mkRegularInstr w q(.imul none $dst $src)
  | `(x64_instr| $op:x64_imul_op $src1:x64_operand, $src2:x64_operand, $dst:x64_reg) =>
    setSuffixWidth op
    let src1 ← elabOperand src1
    let src2 ← elabRegOrMemOperand src2
    let dst ← elabReg dst
    mkRegularInstr w q(.imul (some (.reg $dst)) $src2 $src1)
  | `(x64_instr| $op:x64_mulx_op $src:x64_operand, $lo:x64_reg, $hi:x64_reg) =>
    setSuffixWidth op
    let src ← elabRegOrMemOperand src
    let lo ← elabReg lo
    let hi ← elabReg hi
    mkRegularInstr w q(.mulx $hi $lo $src)
  | `(x64_instr| movsx $src:x64_reg, $dst:x64_reg) =>
    let dst ← elabReg dst
    let ⟨_, src⟩ ← withFreshOperandWidthUnderCurrent (elabReg (w := ·) src)
    mkRegularInstr w q(.movsx (.reg $dst) (.reg $src))
  | `(x64_instr| movzx $src:x64_reg, $dst:x64_reg) =>
    let dst ← elabReg dst
    let ⟨_, src⟩ ← withFreshOperandWidthUnderCurrent (elabReg (w := ·) src)
    mkRegularInstr w q(.movzx (.reg $dst) (.reg $src))
  | `(x64_instr| $op:x64_ext_mov_op $src:x64_operand, $dst:x64_reg) =>
    let (mk, wSrc, wDst) ← elabExtMovOp op
    setOperandWidth q($wDst)
    let dst ← elabReg dst
    let ⟨_, src⟩ ← withOperandWidth (some wSrc) (elabRegOrMemOperand (w := ·) src)
    mkRegularInstr w q($mk (.reg $dst) $src)
  | `(x64_instr| $op:x64_lea_op $m:x64_mem, $dst:x64_reg) =>
    setSuffixWidth op
    let src ← elabMem m
    let dst ← elabReg dst
    mkRegularInstr w q(.lea $dst $src)
  | `(x64_instr| $op:x64_avx_op $src:x64_avx_operand, $dst:x64_avx_operand) =>
    let w ← getAvxOperandWidth
    let mk ← elabAvxOp op
    let src ← elabAvxRegOrMem src
    let dst ← elabAvxRegOrMem dst
    mkAvxInstr w q($mk $dst $src)
  | `(x64_instr| $op:x64_shift_op $dst:x64_operand) =>
    let mk ← elabShiftOp op
    setSuffixWidth op
    let dst ← elabRegOrMemOperand dst
    mkRegularInstr w q($mk $dst (.imm8 (.int64 1)))
  | `(x64_instr| $op:x64_shift_op $cnt:x64_shift_count, $dst:x64_operand) =>
    let mk ← elabShiftOp op
    setSuffixWidth op
    let cnt : ShiftCountExpr ← evalShiftCount cnt
    let dst ← elabRegOrMemOperand dst
    mkRegularInstr w q($mk $dst $cnt)
  | `(x64_instr| $op:x64_shd_op $cnt:x64_shift_count, $src:x64_reg, $dst:x64_operand) =>
    let mk ← elabShdOp op
    setSuffixWidth op
    let cnt : ShiftCountExpr ← evalShiftCount cnt
    let src ← elabReg src
    let dst ← elabRegOrMemOperand dst
    mkRegularInstr w q($mk $dst $src $cnt)
  | `(x64_instr| $op:x64_bswap_op $dst:x64_reg) =>
    setSuffixWidth op
    let dst ← elabReg dst
    mkRegularInstr w q(.bswap $dst)
  | `(x64_instr| $op:x64_push_op $src:x64_operand) =>
    setSuffixWidth op
    let src ← elabOperand src
    mkRegularInstr w q(.push $src) (ifUndetermined := some .W64)
  | `(x64_instr| $op:x64_pop_op $dst:x64_operand) =>
    setSuffixWidth op
    let dst ← elabRegOrMemOperand dst
    mkRegularInstr w q(.pop $dst) (ifUndetermined := some .W64)
  | `(x64_instr| ret) | `(x64_instr| retq) =>
    return q(.regular .W64 .W64 .ret)
  | `(x64_instr| call $target:x64_operand) | `(x64_instr| callq $target:x64_operand) =>
    setOperandWidth q(.W64)
    let target ← elabRelTarget target
    mkRegularInstr w q(.call $target)
  | `(x64_instr| jmp $target:x64_operand) | `(x64_instr| jmpq $target:x64_operand) =>
    setOperandWidth q(.W64)
    let target ← elabRelTarget target
    mkRegularInstr w q(.jmp $target)
  | `(x64_instr| nop) =>
    return q(.regular .W64 .W64 (.nop 1))
  | `(x64_instr| nop $sz:num) =>
    let sz : Nat := sz.getNat
    return q(.regular .W64 .W64 (.nop $sz))
  | `(x64_instr| $op:x64_jcc_op $lbl:x64_ident) =>
    let cc : CondCode ← evalCondCodeSuffix op
    let target : String ← getAsmIdent lbl
    return q(.regular .W64 .W64 (.jcc $cc $target))
  | _ => throwError "invalid instruction syntax"

-- ============================================================================
-- Directive & Program Elaboration
-- ============================================================================

/-- Elaborate an `x64_directive` syntax node into a `Q(Directive)`. -/
def elabDirective (stx : TSyntax `x64_directive) : TermElabM Q(Directive) := withRef stx do
  match stx with
  | `(x64_directive| $lbl:x64_ident :)
  | `(x64_directive| $lbl:x64_ident : ;) =>
    let name : String ← getAsmIdent lbl
    pure q(Directive.label $name)
  | `(x64_directive| $ins:x64_instr ;)
  | `(x64_directive| $ins:x64_instr) =>
    let ins ← (elabInstr ins).run
    return q(Directive.instr $ins)
  | `(x64_directive| ❰ $t ❱ ;)
  | `(x64_directive| ❰ $t ❱) =>
    -- A statement-level antiquotation shadows the instruction-level one, so accept an `Instr` here too.
    let e ← withoutErrToSorry <| withSynthesize <| elabTerm t none
    if ← isDefEq (← inferType e) q(Instr) then
      let ins : Q(Instr) := e
      return q(Directive.instr $ins)
    ensureHasType q(Directive) e
  | _ => throwError "invalid assembly directive"

/-- Elaborate an `x64_prog` syntax node into a `Q(Program)` (`Q(List Directive)`). -/
def elabProgram (stx : TSyntax `x64_prog) : TermElabM Q(Program) := withRef stx do
  match stx with
  | `(x64_prog| $dirs:x64_directive*) =>
    let dirExprs ← dirs.mapM elabDirective
    return dirExprs.foldr (fun d acc => q($d :: $acc)) q([])
  | _ => throwError "invalid assembly program"

-- ============================================================================
-- Public String Parser/Elaborator & Macros
-- ============================================================================

/-- Parse and elaborate an X64 assembly string (with `# ...` line comments) into a `Q(Program)`. -/
public def elabX64 (s : String) : TermElabM Q(Program) :=
  elabCategory `x64_prog elabProgram (replaceLineComments "#" s)

end

/-- Inline unquoted X64 assembly block macro/elaborator (`[x64| ... ]`). -/
elab "[x64|" p:x64_prog "]" : term => elabProgram p

/-- Inline unquoted X64 assembly block macro/elaborator (`parse( ... )`). -/
elab "parse(" p:x64_prog ")" : term => elabProgram p

/-- Compile-time X64 string parser/elaborator (`parse("...")`). -/
elab "parse(" s:str ")" : term => do
  withRef s <| elabX64 s.getString

/-- Read a file at elaboration time and return its contents as a string literal. -/
elab "fileAsString(" path:str ")" : term => do
  let contents : String ← IO.FS.readFile path.getString
  return q($contents)

/-- Read an X64 assembly file, strip assembler directives, parse via `runParserCategory`,
    and elaborate into a Kraken `Program`. -/
elab "include_x64" path:str : term => do
  let content ← IO.FS.readFile path.getString
  withRef path <| elabX64 (stripDirectives content)

end Kraken.X64.Parser
