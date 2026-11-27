module

public meta import Lean

/-!
# `@[lens_simp]` Attribute Registration

Registers the `Optic.Tactic.lensSimpExt` `SimpExtension` and the `@[lens_simp]` attribute syntax
in its own module so `Lens.Tactics.Simp` can immediately tag core optic lemmas with
`attribute [lens_simp] ...`.
-/

public meta section

open Lean Meta

namespace Optic.Tactic

/-- `SimpExtension` storing `@[lens_simp]` rewrite lemmas for normalizing optic expressions. -/
initialize lensSimpExt : SimpExtension ←
  registerSimpAttr `lens_simp "simp lemmas for normalizing optic expressions"

end Optic.Tactic

end

public section

/-- Attribute syntax for `@[lens_simp]`. -/
syntax (name := Lean.Parser.Attr.lens_simp) "lens_simp"
  (Lean.Parser.Tactic.simpPre <|> Lean.Parser.Tactic.simpPost)?
  unicode(" ←", " <-")? (prio)? : attr

end
