module

public import Lens.Basic
public import Lens.Frame
public import Lens.ProdFrame
public meta import Lean

/-!
# Extra Notation & Dot-Path Elaboration for `Lens`

Centralizes all scoped syntax, macros, and dot-path elaborators for the `Lens` library:
- `Optic.Notation`: Haskell-inspired operators (`&`, `^.`, `.~`, `%~`, `∘ₗ`, `×ₗ`, `∘ᵢ`, `∘ᵍ`),
  structure-update style lens pipelines (`{ₗ st with a.b := v, c over f }`), and baseline frame
  syntax (`≡ₗ … on/except […]`).
- `Optic.ProdNotation`: product-lens closure frame syntax (`≡ₚ … on/except […]` and
  `st is { s₀ with … except … }`), backed by `ReflTransGen (Modifies (l₁ ×ₗ … ×ₗ lₖ))`.
-/

@[expose] public section

namespace Optic

universe u v w

namespace Notation

/-- Reverse function application helper. -/
abbrev pipe {α : Type u} {β : Type v} (x : α) (f : α → β) : β := f x

/-- Polymorphic view helper. -/
abbrev viewOf {O : Type u} {s : Type v} {a : Type w} [HasGet O s a] (x : s) (o : O) : a :=
  HasGet.getOf o x

/-- Setter helper for `.~`. -/
abbrev setOf {s : Type u} {a : Type v} (l : Lens s a) (v : a) (x : s) : s :=
  l.set x v

/-- Modifier helper for `%~`. -/
abbrev overOf {s : Type u} {a : Type v} (l : Lens s a) (f : a → a) (x : s) : s :=
  l.over f x

/-- Reverse function application (Haskell `Data.Function.(&)`), for chaining updates:
`s & l₁ .~ v₁ & l₂ %~ f`. -/
scoped infixl:15 " & " => pipe

/-- View through a `Lens`, `Getter`, or `Iso` (Haskell `lens`: `^.`).
Also supports dot-separated field paths (e.g. `st ^. data.regs.x0`). -/
scoped syntax:80 term:80 " ^. " term:81 : term

/-- Set through a `Lens` (Haskell `lens`: `.~`). -/
scoped infixr:40 " .~ " => setOf

/-- Modify through a `Lens` (Haskell `lens`: `%~`). -/
scoped infixr:40 " %~ " => overOf

/-- Outer-to-inner `Lens` composition. -/
scoped infixr:90 " ∘ₗ " => Lens.comp

/-- Product of two lenses on the same source. -/
scoped infixr:85 " ×ₗ " => Lens.prod

/-- Outer-to-inner `Iso` composition. -/
scoped infixr:90 " ∘ᵢ " => Iso.comp

/-- Outer-to-inner `Getter` composition. -/
scoped infixr:90 " ∘ᵍ " => Getter.comp

/-- A single lens update clause inside `{ₗ st with … }` or `st is { st' with … }`. -/
declare_syntax_cat lensUpdate

/-- Set a lens to a new value (`l := v`). -/
scoped syntax term " := " term : lensUpdate

/-- Modify a lens with a function (`l over f`). -/
scoped syntax term " over " term : lensUpdate

/-- Apply a comma-separated pipeline of lens updates, mirroring Lean's structure update syntax:
`{ₗ st with data.regs.x0 := 42, data.flags.z over not}`.
Supports both dot-separated field paths and arbitrary `Lens` expressions. -/
scoped syntax "{ₗ " term " with " lensUpdate,+ " }" : term

/-- `s' ≡ₗ s on [g₁, g₂, …]`: `s'` and `s` agree on all listed getters, lenses, or functions. -/
scoped syntax:50 term:51 " ≡ₗ " term:51 " on " "[" term,* "]" : term

/-- `s' ≡ₗ s except [l₁, l₂, …]`: `s'` differs from `s` only on the listed lenses. -/
scoped syntax:50 term:51 " ≡ₗ " term:51 " except " "[" term,* "]" : term

macro_rules
  | `($s':term ≡ₗ $s:term on [$gs:term,*]) => do
    let items ← gs.getElems.mapM fun g => `(Optic.ToAnyGetter.toAnyGetter $g)
    `(Optic.EqOnAll [$items,*] $s' $s)
  | `($s':term ≡ₗ $s:term except [$ls:term,*]) => do
    let items ← ls.getElems.mapM fun l => `(Optic.ToAnyLens.toAnyLens $l)
    `(Optic.ModifiesAny [$items,*] $s' $s)

end Notation

namespace ProdNotation

open scoped Optic.Notation

/-- `s' ≡ₚ s on [g₁, g₂, …]`: preservation frame (`EqOnAll`). -/
scoped syntax:50 term:51 " ≡ₚ " term:51 " on " "[" term,* "]" : term

/-- `s' ≡ₚ s except [l₁, l₂, …]`: `s'` is reachable from `s` by modifying only the listed lenses
(`ReflTransGen (Modifies (l₁ ×ₗ … ×ₗ lₖ))`, with `Lens.unit` when empty). -/
scoped syntax:50 term:51 " ≡ₚ " term:51 " except " "[" term,* "]" : term

/-- `st is { st' with l₁ := v₁, l₂ over f₂ except e₁, e₂ }`: `st` agrees with the updated state
`{ₗ st' with l₁ := v₁, l₂ over f₂}` everywhere except on `e₁, e₂`. -/
scoped syntax:50 term:51 " is " "{" term " with " lensUpdate,+ " except " term,+ "}" : term

/-- `st is { st' with l₁ := v₁, l₂ over f₂ }`: `st` equals `{ₗ st' with l₁ := v₁, l₂ over f₂}`. -/
scoped syntax:50 term:51 " is " "{" term " with " lensUpdate,+ "}" : term

/-- `st is { st' except e₁, e₂ }`: `st` agrees with `st'` everywhere except on `e₁, e₂`. -/
scoped syntax:50 term:51 " is " "{" term " except " term,+ "}" : term

macro_rules
  | `($s':term ≡ₚ $s:term on [$gs:term,*]) => do
    let items ← gs.getElems.mapM fun g => `(Optic.ToAnyGetter.toAnyGetter $g)
    `(Optic.EqOnAll [$items,*] $s' $s)
  | `($s':term ≡ₚ $s:term except []) =>
    `(Optic.ReflTransGen (Optic.Modifies Optic.Lens.unit.{_, 0}) $s' $s)
  | `($s':term ≡ₚ $s:term except [$l:term]) =>
    `(Optic.ReflTransGen (Optic.Modifies $l) $s' $s)
  | `($s':term ≡ₚ $s:term except [$l:term, $ls:term,*]) => do
    let elems := #[l] ++ ls.getElems
    let mut prod := elems[elems.size - 1]!
    for i in [1:elems.size] do
      let idx := elems.size - 1 - i
      prod ← `(Optic.Lens.prod $(elems[idx]!) $prod)
    `(Optic.ReflTransGen (Optic.Modifies $prod) $s' $s)

end ProdNotation

end Optic

end

public meta section

open Lean Meta Elab Term

namespace Optic.ExtraNotation

open scoped Optic.Notation Optic.ProdNotation

/-- Resolve a dot-separated field path `a.b.c` starting from source type `sTy` by looking up
`<TypeName>.Lenses.<seg>` at each step and composing with `Optic.Lens.comp`. Returns `none` if
`stx` is not an identifier or any segment is not found in `<TypeName>.Lenses`. -/
private def resolveLensPath? (sTy : Expr) (stx : Term) : TermElabM (Option Expr) := do
  unless stx.raw.isIdent do return none
  let segs := stx.raw.getId.components
  if segs.isEmpty then return none
  let saved ← saveState
  -- NOTE: We could just use `commitWhenSomeNoEx?` here, no?
  try
    let mut curTy ← instantiateMVars sTy
    let mut acc : Option Expr := none
    for seg in segs do
      let curTyWhnf ← whnf curTy
      let .const typeName _ := curTyWhnf.getAppFn | saved.restore; return none
      let lensName := typeName ++ `Lenses ++ seg
      unless (← getEnv).contains lensName do
        saved.restore
        return none
      let stepLens ← mkAppOptM lensName (curTyWhnf.getAppArgs.map some)
      let stepTy ← whnf (← inferType stepLens)
      unless stepTy.isAppOfArity ``Optic.Lens 2 do
        saved.restore
        return none
      acc ← match acc with
        | none => pure (some stepLens)
        | some prev => pure (some (← mkAppM ``Optic.Lens.comp #[prev, stepLens]))
      curTy ← instantiateMVars (stepTy.getArg! 1)
    return acc
  catch _ =>
    saved.restore
    return none

/-- Elaborate a single `lensUpdate` (`l := v` or `l over f`) applied to state `acc : sTy`. -/
private def elabLensUpdate (sTy : Expr) (acc : Expr) (u : TSyntax `lensUpdate) : TermElabM Expr := do
  match u with
  | `(lensUpdate| $l:term := $v:term) => do
    let lensE ← (← resolveLensPath? sTy l).getDM (elabTerm l none)
    let lensTy ← whnf (← inferType lensE)
    let valTy := if lensTy.isAppOfArity ``Optic.Lens 2 then some (lensTy.getArg! 1) else none
    let valE ← elabTerm v valTy
    mkAppM ``Optic.Lens.set #[lensE, acc, valE]
  | `(lensUpdate| $l:term over $f:term) => do
    let lensE ← (← resolveLensPath? sTy l).getDM (elabTerm l none)
    let lensTy ← whnf (← inferType lensE)
    let fnTy ← if lensTy.isAppOfArity ``Optic.Lens 2 then
        let a := lensTy.getArg! 1
        pure (some (← mkArrow a a))
      else pure none
    let fnE ← elabTerm f fnTy
    mkAppM ``Optic.Lens.over #[lensE, fnE, acc]
  | _ => throwUnsupportedSyntax

/-- Elaborate a non-empty list of `except` entries as a right-associated product `Lens sTy _`,
trying dot-path lens resolution first on each entry. -/
private def elabExceptProdLens (sTy : Expr) (es : Array Term) : TermElabM Expr := do
  let lenses ← es.mapM fun e => do
    (← resolveLensPath? sTy e).getDM (elabTerm e none)
  let mut prod := lenses[lenses.size - 1]!
  for i in [1:lenses.size] do
    let idx := lenses.size - 1 - i
    prod ← mkAppM ``Optic.Lens.prod #[lenses[idx]!, prod]
  return prod

elab_rules : term
  | `($x:term ^. $o:term) => do
    let xE ← elabTerm x none
    let sTy ← instantiateMVars (← inferType xE)
    match ← resolveLensPath? sTy o with
    | some lensE => mkAppM ``Optic.Lens.get #[lensE, xE]
    | none =>
      let oE ← elabTerm o none
      mkAppM ``Optic.Notation.viewOf #[xE, oE]
  | `({ₗ $s:term with $us:lensUpdate,* }) => do
    let mut acc ← elabTerm s none
    let sTy ← instantiateMVars (← inferType acc)
    for u in us.getElems do
      acc ← elabLensUpdate sTy acc u
    return acc
  | `($st:term is { $st':term with $us:lensUpdate,* except $es:term,* }) => do
    let stE ← elabTerm st none
    let sTy ← instantiateMVars (← inferType stE)
    let mut updated ← elabTermEnsuringType st' sTy
    for u in us.getElems do
      updated ← elabLensUpdate sTy updated u
    let prodLens ← elabExceptProdLens sTy es.getElems
    let modRel ← mkAppM ``Optic.Modifies #[prodLens]
    mkAppM ``Optic.ReflTransGen #[modRel, stE, updated]
  | `($st:term is { $st':term with $us:lensUpdate,* }) => do
    let stE ← elabTerm st none
    let sTy ← instantiateMVars (← inferType stE)
    let mut updated ← elabTermEnsuringType st' sTy
    for u in us.getElems do
      updated ← elabLensUpdate sTy updated u
    mkEq stE updated
  | `($st:term is { $st':term except $es:term,* }) => do
    let stE ← elabTerm st none
    let sTy ← instantiateMVars (← inferType stE)
    let st'E ← elabTermEnsuringType st' sTy
    let prodLens ← elabExceptProdLens sTy es.getElems
    let modRel ← mkAppM ``Optic.Modifies #[prodLens]
    mkAppM ``Optic.ReflTransGen #[modRel, stE, st'E]

end Optic.ExtraNotation

end
