module

import Kraken.AArch64.Semantics
meta import Kraken.AArch64.Semantics

/-!
# Semantics Shape and Evaluator Tests (AArch64)

Regression tests for the `grind`/`omega`/`simp`-friendliness of AArch64 flag projections,
condition codes, carry-chain limb identities, `UInt64`/`BitVec`/`Nat` bridging, and the
concrete evaluator.
-/

/-! ### Flag Projections (`@[kcond]`) and Condition Codes -/

example (a b : BitVec 64) : (StatusFlags.subs a b).c = decide (b.toNat ≤ a.toNat) := by simp
example (a b : BitVec 64) : (StatusFlags.subs a b).z = decide (a = b) := by simp
example (a b : BitVec 64) : (StatusFlags.adds a b).c = decide (2 ^ 64 ≤ a.toNat + b.toNat) := by simp
example (a b : BitVec 64) (c : Bool) :
    (StatusFlags.adcs a b c).c = decide (2 ^ 64 ≤ a.toNat + b.toNat + c.toNat) := by simp
example (a b : BitVec 64) (c : Bool) :
    (StatusFlags.sbcs a b c).c = decide (b.toNat + (!c).toNat ≤ a.toNat) := by simp

-- Branch conditions after `subs`/`cmp` simplify directly to value-level comparisons.
example (a b : BitVec 64) : CondCode.interp .CS (StatusFlags.subs a b) = decide (b.toNat ≤ a.toNat) := by
  simp [CondCode.interp]
example (a b : BitVec 64) : CondCode.interp .LT (StatusFlags.subs a b) = decide (a.toInt < b.toInt) := by
  simp [CondCode.interp]
example (a b : BitVec 64) : CondCode.interp .GE (StatusFlags.subs a b) = decide (b.toInt ≤ a.toInt) := by
  simp [CondCode.interp]
example (a b : BitVec 64) : CondCode.interp .GT (StatusFlags.subs a b) = decide (b.toInt < a.toInt) := by
  simp [CondCode.interp]
example (a b : BitVec 64) : CondCode.interp .LE (StatusFlags.subs a b) = decide (a.toInt ≤ b.toInt) := by
  simp [CondCode.interp]
example (a b : BitVec 64) : CondCode.interp .HI (StatusFlags.subs a b) = decide (b.toNat < a.toNat) := by
  simp [CondCode.interp]
example (a b : BitVec 64) : CondCode.interp .LS (StatusFlags.subs a b) = decide (a.toNat ≤ b.toNat) := by
  simp [CondCode.interp]
example (a b : BitVec 64) : CondCode.interp .EQ (StatusFlags.subs a b) = decide (a = b) := by
  simp [CondCode.interp]

-- `cmn xzr, xzr` clears the carry.
example : (StatusFlags.adds 0#64 0#64).c = false := by simp

/-! ### Carry-Chain Limb Identities -/

example (a0 b0 a1 b1 : BitVec 64) (c : Bool) :
    ((a0 + b0 + BitVec.ofNat 64 c.toNat).toNat : Int) +
      2 ^ 64 * (a1 + b1 + BitVec.ofNat 64 ((StatusFlags.adcs a0 b0 c).c).toNat).toNat +
      2 ^ 128 * ((StatusFlags.adcs a1 b1 (StatusFlags.adcs a0 b0 c).c).c).toNat =
      a0.toNat + 2 ^ 64 * a1.toNat + (b0.toNat + 2 ^ 64 * b1.toNat) + c.toNat := by
  have h0 := StatusFlags.adcs_toNat a0 b0 c (by decide)
  have h1 := StatusFlags.adcs_toNat a1 b1 (StatusFlags.adcs a0 b0 c).c (by decide)
  simp only [Nat.reducePow] at h0 h1
  omega

/-! ### Raw Flag Definitions, `UInt64` Registers, and Immediates -/

example (a b : BitVec 64) :
    ((((a - b).toNat : Int) == (a.toNat : Int) - (b.toNat : Int)) = true) ↔ b.toNat ≤ a.toNat := by
  grind

example (a b : BitVec 64) :
    ((((a - b).toInt) != a.toInt - b.toInt) = true) ↔
      ¬ (-(2 ^ 63) ≤ a.toInt - b.toInt ∧ a.toInt - b.toInt < 2 ^ 63) := by
  grind

example (x : UInt64) (h : 1 < x.toNat) : (x.toBitVec - 1#64 == 0#64) = false := by grind
example (x : UInt64) (h : x.toBitVec = 1#64) : x.toNat = 1 := by grind
example (x : UInt64) : (UInt64.ofBitVec (x.toBitVec + 1#64)).toNat = (x.toNat + 1) % 2 ^ 64 := by grind
example (x : UInt64) (h : 0 < x.toNat) : (x.toBitVec != 0#64) = true := by grind

example (x : BitVec 64) : x - BitVec.ofInt 64 1 = x - 1#64 := by grind
example (x : BitVec 64) : x + BitVec.ofInt 64 (Int64.toInt (-112)) = x - 112#64 := by grind

/-! ### Concrete Evaluator Tests -/

/-- info: Except.ok 58 -/
#guard_msgs in
#eval
  let exe := Program.fakeLayout [
    .label "main",
    .instr ⟨.W64, .LDR .X1 (.addr { base := .SP, off := 0 })⟩,
    .instr ⟨.W64, .ADD_e .X1 .X1 0x10⟩,
    .instr ⟨.W64, .STR .X1 { base := .SP, off := 0 }⟩,
    .instr ⟨.W64, .LDR .X2 (.addr { base := .SP, off := 0 })⟩]
  let start := exe.labels.label "main"
  let data : MachineData := { dmem := Mem.storeInt {} 0x100 8 42, regs := { SP := 0x100 } }
  (exe.eval { data, pc := start } (fun st => (exe.directivesFromAddress st.pc).isEmpty)).bind (fun s => .ok s.1.regs.X2)

/-- info: Except.ok (42, 264) -/
#guard_msgs in
#eval
  let exe := Program.fakeLayout [
    .label "main",
    .instr ⟨.W64, .LDR .X1 (.addr { base := .SP, off := .imm { imm := 8, index := some .Pre } })⟩ ]
  let start := exe.labels.label "main"
  let data : MachineData := { dmem := Mem.storeInt {} 0x108 8 42, regs := { SP := 0x100 } }
  (exe.eval { data, pc := start } (fun st => (exe.directivesFromAddress st.pc).isEmpty)).bind (fun s => .ok (s.1.regs.X1, s.1.regs.SP))

/-- info: Except.ok (42, 264) -/
#guard_msgs in
#eval
  let exe := Program.fakeLayout [
    .label "main",
    .instr ⟨.W64, .STR .X1 { base := .SP, off := .imm { imm := 8, index := some .Post } }⟩ ]
  let start := exe.labels.label "main"
  let data : MachineData := { dmem := Mem.storeInt {} 0x100 8 0, regs := { SP := 0x100, X1 := 42 } }
  (exe.eval { data, pc := start } (fun st => (exe.directivesFromAddress st.pc).isEmpty)).bind (fun s =>
    match Mem.loadInt s.1.dmem 0x100 8 with
    | some v => .ok (v, s.1.regs.SP)
    | none => .error "Memory store failed"
  )
