module

public import Kraken.OmniSemantics
public import Kraken.X64.Semantics

/-!
# x86-64 Inert Directives

Re-exports `Directive.Inert` and `Directives.interp_inert_append` from `Kraken.OmniSemantics`
together with x86-64 directive inertness lemmas.
-/

@[expose] public section

@[simp]
theorem Directive.inert_label (l : Label) : Directive.Inert (.label l : Directive) := by
  intro _ _ _ _ _ _
  rfl
