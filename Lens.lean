module

public import Lens.Basic
public import Lens.Relation
public import Lens.Frame
public import Lens.ProdFrame
public import Lens.Family
public import Lens.Derive
public import Lens.Tactics.Disjoint
public import Lens.Tactics.Frame
public import Lens.Tactics.Eqs
public import Lens.ExtraNotation

/-!
# Optics / Lenses Library

Umbrella module re-exporting:
- `Lens.Basic`: `Getter`, `Iso`, `Lens`, `LawfulIso`, `LawfulLens`, `Independent`, `Disjoint`,
  and `HasGet`.
- `Lens.Relation`: standalone reflexive-transitive closure `ReflTransGen` (matching Mathlib's
  `Relation.ReflTransGen`).
- `Lens.Frame`: `EqOn`, `EqOnAll`, `Modifies`, and baseline existential-wrapper frames
  (`AnyGetter`, `AnyLens`, `ModifiesAny`).
- `Lens.ProdFrame`: product-lens frames (`Modifies` over `×ₗ` and `Lens.unit`), `FactorsLawful`,
  and the unconditional closure algebra `ReflTransGen (Modifies …)`.
- `Lens.Family`: indexed `LensFamily` / `LawfulLensFamily` and bridge theorems.
- `Lens.Derive`: `make_lenses` command and `lens_disjoint` tactic.
- `Lens.ExtraNotation`: scoped operators (`Optic.Notation`, `Optic.ProdNotation`), dot-path
  resolution, `{ₗ st with … }`, and `st is { s₀ with … except … }`.
-/
