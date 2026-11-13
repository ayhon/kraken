module

import Kraken.X64.Semantics
meta import Kraken.X64.Semantics

/-!
# Semantics Shape and Evaluator Tests (x86-64)

Regression tests for the `grind`/`omega`/`simp`-friendliness of x86-64 flag projections,
condition codes, carry-chain limb identities, and the concrete evaluator.
-/

/-! ### Memory Access Span Checks -/

private partial def accessChecks :
    Effects → Option (List (Nat × Nat) × List (Nat × Nat))
  | .done _ => some ([], [])
  | .require_read_access p ok => (accessChecks (ok ())).map fun (rs, ws) => ((p.lower.val, p.upper.val) :: rs, ws)
  | .require_write_access p ok => (accessChecks (ok ())).map fun (rs, ws) => (rs, (p.lower.val, p.upper.val) :: ws)
  | _ => none

/-- 64 bytes of data memory at `0x1000`. -/
private def s : MachineData := { dmem := (List.replicate 64 0).At 0x1000 }

#guard accessChecks (s.loadAvx 0x1000 .W128 fun _ s => .done ⟨s, 0⟩) ==
  some ([(0x1000, 0x1010)], [])
#guard accessChecks (s.loadAvx 0x1000 .W256 fun _ s => .done ⟨s, 0⟩) ==
  some ([(0x1000, 0x1020)], [])
#guard accessChecks (s.loadAvx 0x1000 .W512 fun _ s => .done ⟨s, 0⟩) ==
  some ([(0x1000, 0x1040)], [])
#guard accessChecks (s.storeAvx (w := .W128) 0x1000 0 fun s => .done ⟨s, 0⟩) ==
  some ([], [(0x1000, 0x1010)])
#guard accessChecks (s.storeAvx (w := .W256) 0x1000 0 fun s => .done ⟨s, 0⟩) ==
  some ([], [(0x1000, 0x1020)])
#guard accessChecks (s.storeAvx (w := .W512) 0x1000 0 fun s => .done ⟨s, 0⟩) ==
  some ([], [(0x1000, 0x1040)])

#guard ([Width.W8, .W16, .W32, .W64].all fun w =>
  accessChecks (MachineData.load s 0x1000 w fun _ s => .done ⟨s, 0⟩) ==
    some ([(0x1000, 0x1000 + w.bytes)], []) &&
  accessChecks (MachineData.store (w := w) s 0x1000 0 fun s => .done ⟨s, 0⟩) ==
    some ([], [(0x1000, 0x1000 + w.bytes)]))

#guard accessChecks (s.loadAvx 0x1001 .W128 fun _ s => .done ⟨s, 0⟩) ==
  some ([(0x1001, 0x1011)], [])
#guard match s.loadAvx 0x1001 .W128 (fun _ s => .done ⟨s, 0⟩) (checkAlign := true) with
  | .unaligned addr bytes => addr == 0x1001 && bytes == 16
  | _ => false
#guard match s.storeAvx (w := .W128) 0x1001 0 (fun s => .done ⟨s, 0⟩) (checkAlign := true) with
  | .unaligned addr bytes => addr == 0x1001 && bytes == 16
  | _ => false

private def wrapping : MachineData :=
  { dmem := (List.replicate 64 0).At 0xfffffffffffffff8 }

#guard accessChecks (MachineData.load wrapping 0xffffffffffffffff .W8 fun _ s => .done ⟨s, 0⟩) ==
  some ([(0xffffffffffffffff, UInt64.size)], [])
#guard accessChecks (wrapping.loadAvx 0xfffffffffffffff8 .W128 fun _ s => .done ⟨s, 0⟩) ==
  some ([(0xfffffffffffffff8, UInt64.size), (0, 8)], [])
#guard accessChecks (wrapping.storeAvx (w := .W128) 0xfffffffffffffff8 0 fun s => .done ⟨s, 0⟩) ==
  some ([], [(0xfffffffffffffff8, UInt64.size), (0, 8)])

/-! ### `cld`/`std` Direction Flag Checks -/

private def runOp (op : Operation .W64) (s : MachineData) : Option MachineData :=
  let : Labels := ⟨fun _ => 0⟩
  let : AddressSize := ⟨.W64⟩
  match op.interp ⟨0, 1⟩ s (fun s => .done ⟨s, 1⟩) (fun _ _ => .unimplemented "jump") with
  | .done st => some st.data
  | _ => none

/-- A state with every status flag set and some register and memory contents. -/
private def busy : MachineData :=
  { s with regs := { rax := 7 }, status := .mk true true true true true true }

#guard runOp .std busy == some { busy with df := true }
#guard runOp .cld { busy with df := true } == some busy
#guard runOp .cld busy == some busy
#guard (runOp .std busy >>= runOp .std) == some { busy with df := true }
#guard (runOp .std busy >>= runOp .cld) == some busy

/-! ### Flag Projections (`@[kcond]`) and Condition Codes -/

example (a b : BitVec 64) : (StatusFlags.sub a b).cf = decide (a.toNat < b.toNat) := by simp
example (a b : BitVec 64) : (StatusFlags.sub a b).zf = decide (a = b) := by simp
example (a b : BitVec 64) : (StatusFlags.add a b).cf = decide (2 ^ 64 ≤ a.toNat + b.toNat) := by simp
example (a b : BitVec 64) (c : Bool) :
    (StatusFlags.adc a b c).cf = decide (2 ^ 64 ≤ a.toNat + b.toNat + c.toNat) := by simp
example (a b : BitVec 64) (c : Bool) :
    (StatusFlags.sbb a b c).cf = decide (a.toNat < b.toNat + c.toNat) := by simp
example (a : BitVec 64) (cf : Bool) : (StatusFlags.dec a cf).zf = decide (a = 1#64) := by simp
example (a : BitVec 64) (cf : Bool) : (StatusFlags.dec a cf).cf = cf := by simp
example (v : BitVec 64) (af : Bool) : (StatusFlags.logical v af).zf = decide (v = 0#64) := by simp

-- Branch conditions after `cmp a, b` simplify directly to value-level comparisons.
example (a b : BitVec 64) : CondCode.interp .c (StatusFlags.sub a b) = decide (a.toNat < b.toNat) := by
  simp [CondCode.interp]
example (a b : BitVec 64) : CondCode.interp .be (StatusFlags.sub a b) = decide (a.toNat ≤ b.toNat) := by
  simp [CondCode.interp]
example (a b : BitVec 64) : CondCode.interp .a (StatusFlags.sub a b) = decide (b.toNat < a.toNat) := by
  simp [CondCode.interp]
example (a b : BitVec 64) : CondCode.interp .l (StatusFlags.sub a b) = decide (a.toInt < b.toInt) := by
  simp [CondCode.interp]
example (a b : BitVec 64) : CondCode.interp .ge (StatusFlags.sub a b) = decide (b.toInt ≤ a.toInt) := by
  simp [CondCode.interp]
example (a b : BitVec 64) : CondCode.interp .g (StatusFlags.sub a b) = decide (b.toInt < a.toInt) := by
  simp [CondCode.interp]
example (a b : BitVec 64) : CondCode.interp .le (StatusFlags.sub a b) = decide (a.toInt ≤ b.toInt) := by
  simp [CondCode.interp]
example (a b : BitVec 64) : CondCode.interp .z (StatusFlags.sub a b) = decide (a = b) := by
  simp [CondCode.interp]

/-! ### Carry-Chain Limb Identities -/

example (a0 b0 a1 b1 : BitVec 64) (c : Bool) :
    ((a0 + b0 + BitVec.ofNat 64 c.toNat).toNat : Int) +
      2 ^ 64 * (a1 + b1 + BitVec.ofNat 64 ((StatusFlags.adc a0 b0 c).cf).toNat).toNat +
      2 ^ 128 * ((StatusFlags.adc a1 b1 (StatusFlags.adc a0 b0 c).cf).cf).toNat =
      a0.toNat + 2 ^ 64 * a1.toNat + (b0.toNat + 2 ^ 64 * b1.toNat) + c.toNat := by
  have h0 := StatusFlags.adc_toNat a0 b0 c (by decide)
  have h1 := StatusFlags.adc_toNat a1 b1 (StatusFlags.adc a0 b0 c).cf (by decide)
  simp only [Nat.reducePow] at h0 h1
  omega

/-! ### Concrete Evaluator Tests -/

/-- info: Except.ok 42 -/
#guard_msgs in
#eval
  let exe := Program.fakeLayout [
    .label "main",
    .instr (.regular .W64 .W64 (.lea (.low .rax .W64) (.mk .none .none (.int64 41)))),
    .instr (.regular .W64 .W64 (.inc (.reg (.low .rax .W64)))),
    .instr (.regular .W64 .W64 .ret) ]
  let start := exe.labels.label "main"
  let data : MachineData := { dmem := Mem.storeInt {} 0x100 8 0x1337, regs := { rsp := 0x100 } }
  (exe.eval { data, pc := start } (fun st => st.pc = 0x1337)).bind (fun s => .ok s.1.regs.rax)
