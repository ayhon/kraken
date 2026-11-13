module

public meta import Lean

/-!
# Kraken Tactic Attributes

Custom attributes used by Kraken's symbolic execution and verification tactics:
- `@[kstep]`: definitions and theorems unfolded or reduced during instruction stepping.
- `@[kspec]`: separation-logic specification lemmas for built-in memory operations.
- `@[ksimp]`: simplification rules applied by `kstep` during symbolic execution.
- `@[kcond]`: simplification rules presenting processor flags and branch conditions at the value level.
-/

public meta section

open Lean Lean.Meta

initialize kstepExtension : SimpleScopedEnvExtension Name NameSet ←
  registerSimpleScopedEnvExtension {
    name := `kstepExtension
    addEntry := fun s n => s.insert n
    initial := {}
  }

/-- Declarations reduced in the goal as part of the `kstep` tactic. -/
initialize registerBuiltinAttribute {
  name := `kstep
  descr := "declarations to be reduced in the goal as part of the kstep tactic"
  add := fun declName _stx _kind => do
    modifyEnv fun env => kstepExtension.addEntry env declName
}

initialize kspecExtension : SimpleScopedEnvExtension Name NameSet ←
  registerSimpleScopedEnvExtension {
    name := `kspecExtension
    addEntry := fun s n => s.insert n
    initial := {}
  }

/-- Separation-logic specification lemmas for built-in operations used by `kstep`. -/
initialize registerBuiltinAttribute {
  name := `kspec
  descr := "specification lemmas for built-in, in separation logic, to be leveraged by the kstep tactic"
  add := fun declName _stx _kind => do
    modifyEnv fun env => kspecExtension.addEntry env declName
}

/-- Simp theorems used by `kstep` to normalize symbolic state expressions. -/
initialize ksimpExt : Sym.Simp.SymSimpExtension ←
  Sym.Simp.registerSymSimpAttr `ksimp "simp theorems used by kstep"

/-- Simp lemmas that present processor flags and branch conditions at the value level, e.g.
`(StatusFlags.subs a b).c = decide (b.toNat ≤ a.toNat)`. Used by `kstep` when deciding a branch
condition and by `kfinish`, while keeping flag functions folded during stepping. -/
initialize kcondExt : SimpExtension ←
  registerSimpAttr `kcond "simp lemmas presenting flags and branch conditions at the value level"

end
