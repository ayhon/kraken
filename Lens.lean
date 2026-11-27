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
public import Lens.Tactics.Simp
public import Lens.ExtraNotation
public import Lens.Tactics.Notation

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
- `Lens.Derive`: `make_lenses` command and `lensFieldExt` field-lens metadata registry.
- `Lens.Tactics.Disjoint`: path-aware `lens_disjoint` / `lens_indep` tactics and `@[lens_disjoint]`
  / `@[lens_indep]` extensible attributes.
- `Lens.Tactics.Frame`: `lens_frame` tactic (symbolic diffs, frame-algebra graph search, and
  `EqOn`/`EqOnAll` narrowing).
- `Lens.Tactics.Eqs`: demand-driven `lens_eqs`, `lens_rw` simproc, and `frameEqsFor` /
  `frameEqsInContext` APIs.
- `Lens.Tactics.Simp`: `lens_simp`, `lens_dsimp`, and `@[lens_simp]` optic normalization.
- `Lens.ExtraNotation` & `Lens.Tactics.Notation`: scoped operators (`Optic.Notation`,
  `Optic.ProdNotation`), dot-path elaboration for `^.`, `{ₗ … with … }`, `is { … }`,
  `≡ₚ … except/on […]`, and `@[app_unexpander]` pretty-printers.
-/
