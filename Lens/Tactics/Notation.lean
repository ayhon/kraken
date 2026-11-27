module

public import Lens.Basic
public import Lens.Frame
public import Lens.ProdFrame
public import Lens.Derive
public import Lens.ExtraNotation
public meta import Lean

/-!
# Dot-Path Frame Elaboration & Pretty-Printing (`≡ₚ … except/on […]`)

Provides:
- Dot-path term elaborators for `s' ≡ₚ s except […]` and `s' ≡ₚ s on […]` (syntax declared in
  `Optic.ProdNotation` in `Lens.ExtraNotation`):
  - `s' ≡ₚ s except []` elaborates to `Optic.ReflTransGen (Optic.Modifies (Optic.Lens.unit.{u, 0} (s := sTy))) s' s`.
  - `s' ≡ₚ s except [e₁, e₂, …]` resolves dot-paths (`pc`, `data.regs.x0`, `data.flags.z`, …) via
    `Optic.ExtraNotation.resolveLensPath?` and falls back to arbitrary `Lens` / `Iso` expressions,
    building a right-associated `Lens.prod` tree inside `ReflTransGen (Modifies …)`.
  - `s' ≡ₚ s on [g₁, g₂, …]` resolves dot-paths (wrapping via `AnyGetter.ofLens`), nested dot-path
    struct views (`data.regs.viewA`), struct-namespaced views (`viewA` → `MiniRegs.viewA`), and
    arbitrary `Getter` / `Lens` / `Iso` / function / lambda expressions via `ToAnyGetter.toAnyGetter`
    or `AnyGetter.ofFn`.
- `@[app_unexpander]` pretty-printers for `Optic.ReflTransGen` (when applied to `Optic.Modifies …`)
  and `Optic.EqOnAll`, rendering `StructName.Lenses.<field>` chains as readable dot-paths and
  flattening `Lens.prod` trees into concise `s' ≡ₚ s except […]` and `s' ≡ₚ s on […]` notation.
-/

public meta section

open Lean Meta Elab Term PrettyPrinter

namespace Optic.Tactics.Notation

open scoped Optic.Notation Optic.ProdNotation

/-! ### Speculative Elaboration & `on […]` Entry Resolution -/

/-- Normalize built-in `Optic.ToAnyGetter.toAnyGetter` applications directly into their reducible
`AnyGetter` constructors (`ofLens`, `of`, `ofIso`, `ofFn`, or identity) so downstream optics
tactics (such as `lens_indep`) see the underlying optic without unfolding typeclass projections. -/
private def simplifyToAnyGetter (e : Expr) : MetaM Expr := do
  unless e.isAppOfArity ``Optic.ToAnyGetter.toAnyGetter 4 do
    return e
  let arg := e.getArg! 3
  let argTy ← whnf (← inferType arg)
  if argTy.isAppOfArity ``Optic.Lens 2 then
    mkAppM ``Optic.AnyGetter.ofLens #[arg]
  else if argTy.isAppOfArity ``Optic.Getter 2 then
    mkAppM ``Optic.AnyGetter.of #[arg]
  else if argTy.isAppOfArity ``Optic.Iso 2 then
    mkAppM ``Optic.AnyGetter.ofIso #[arg]
  else if argTy.isAppOfArity ``Optic.AnyGetter 1 then
    return arg
  else if argTy.isArrow then
    mkAppM ``Optic.AnyGetter.ofFn #[arg]
  else
    return e

/-- Try elaborating `stx` into `AnyGetter.{u, v} sTy`, first via `Optic.ToAnyGetter.toAnyGetter`
(covering `Getter`, `Lens`, `Iso`, `AnyGetter`, and named functions) and then as a function
`sTy → ?α` wrapped in `Optic.AnyGetter.ofFn` (so untyped lambdas like `fun st => st.pc` receive
the expected source type `sTy`). -/
private def elabViewOnType? (sTy : Expr) (u v : Level) (stx : Term) : TermElabM (Option Expr) := do
  let anyGetterTy := mkApp (mkConst ``Optic.AnyGetter [u, v]) sTy
  if let some e ← Optic.ExtraNotation.tryTermElab? do
      let appStx ← `(Optic.ToAnyGetter.toAnyGetter $stx)
      let raw ← elabTermEnsuringType appStx anyGetterTy
      let simplified ← simplifyToAnyGetter raw
      unless ← isDefEq (← inferType simplified) anyGetterTy do
        return raw
      return simplified then
    return some e
  Optic.ExtraNotation.tryTermElab? do
    let α ← mkFreshExprMVar (mkSort (.succ v))
    let fnTy ← mkArrow sTy α
    let fnE ← elabTermEnsuringType stx fnTy
    let res ← mkAppM ``Optic.AnyGetter.ofFn #[fnE]
    unless ← isDefEq (← inferType res) anyGetterTy do
      throwError "expected `AnyGetter` in universe `{v}`"
    return res

/-- Try resolving an identifier `id` in the namespace of the head constant of `sTy`
(e.g. `viewA` ↦ `MiniRegs.viewA` on `MiniRegs`), returning `AnyGetter.{u, v} sTy`. -/
private def resolveStructView? (sTy : Expr) (u v : Level) (id : Ident) : TermElabM (Option Expr) := do
  let sTyWhnf ← whnf sTy
  let .const sName _ := sTyWhnf.getAppFn | return none
  let candName := sName ++ id.getId.eraseMacroScopes
  unless (← getEnv).contains candName do
    return none
  let candIdent := mkIdentFrom id (`_root_ ++ candName)
  elabViewOnType? sTy u v candIdent

/-- Try resolving a multi-segment dot-path `a₁.…aₖ.view` whose prefix `a₁.…aₖ` is a lens path on
`sTy` and whose final segment `view` resolves in the namespace of the inner focus type
(e.g. `data.regs.viewA` on `MiniState MiniMachineData`). -/
private def resolveNestedLensView? (sTy : Expr) (u v : Level) (stx : Term) :
    TermElabM (Option Expr) := do
  unless stx.raw.isIdent do return none
  let segs := stx.raw.getId.eraseMacroScopes.components
  unless segs.length ≥ 2 do return none
  let prefixName := segs.dropLast.foldl (· ++ ·) Name.anonymous
  let lastSeg := segs.getLast!
  let prefixIdent := mkIdentFrom stx prefixName
  let lastIdent := mkIdentFrom stx lastSeg
  let anyGetterTy := mkApp (mkConst ``Optic.AnyGetter [u, v]) sTy
  commitWhenSomeNoEx? do
    let some outerLens ← Optic.ExtraNotation.resolveLensPath? sTy prefixIdent | return none
    let outerTy ← whnf (← inferType outerLens)
    unless outerTy.isAppOfArity ``Optic.Lens 2 do return none
    let innerTy ← instantiateMVars (outerTy.getArg! 1)
    let uInner ← getDecLevel innerTy
    let some innerGetter ← resolveStructView? innerTy uInner v lastIdent | return none
    let outerGetter ← mkAppM ``Optic.Lens.toGetter #[outerLens]
    let res ← mkAppM ``Optic.AnyGetter.comp #[outerGetter, innerGetter]
    unless ← isDefEq (← inferType res) anyGetterTy do return none
    return some res

/-- Elaborate a single entry `g` of `s' ≡ₚ s on […]` into `Optic.AnyGetter.{u, v} sTy`. -/
def elabAnyGetter (sTy : Expr) (u v : Level) (g : Term) : TermElabM Expr := do
  let anyGetterTy := mkApp (mkConst ``Optic.AnyGetter [u, v]) sTy
  -- 1. Pure dot-path lens (e.g. `pc`, `data.regs.x0`)
  if let some lensE ← Optic.ExtraNotation.resolveLensPath? sTy g then
    let res ← mkAppM ``Optic.AnyGetter.ofLens #[lensE]
    if ← isDefEq (← inferType res) anyGetterTy then
      return res
  -- 2. Nested dot-path ending in a struct-namespaced view (e.g. `data.regs.viewA`)
  if let some res ← resolveNestedLensView? sTy u v g then
    return res
  -- 3. Struct-namespaced view on `sTy` (e.g. `viewA` ↦ `MiniRegs.viewA`)
  if g.raw.isIdent then
    if let some res ← resolveStructView? sTy u v ⟨g.raw⟩ then
      return res
  -- 4. Arbitrary `ToAnyGetter` optic/function or lambda `fun st => ...`
  if let some res ← elabViewOnType? sTy u v g then
    return res
  -- Fallback: emit the standard elaboration error at `g`
  let appStx ← `(Optic.ToAnyGetter.toAnyGetter $g)
  elabTermEnsuringType appStx anyGetterTy

/-! ### Dot-Path `elab_rules` for `≡ₚ … except […]` and `≡ₚ … on […]` -/

elab_rules : term
  | `($s':term ≡ₚ $s:term except [$es:term,*]) => do
    let s'E ← elabTerm s' none
    let sTy' ← instantiateMVars (← inferType s'E)
    let sE ← elabTermEnsuringType s sTy'
    let sTy ← instantiateMVars (← inferType s'E)
    let prodLens ← Optic.ExtraNotation.elabExceptProdLens sTy es.getElems
    let modRel ← mkAppM ``Optic.Modifies #[prodLens]
    mkAppM ``Optic.ReflTransGen #[modRel, s'E, sE]
  | `($s':term ≡ₚ $s:term on [$gs:term,*]) => do
    let s'E ← elabTerm s' none
    let sTy' ← instantiateMVars (← inferType s'E)
    let sE ← elabTermEnsuringType s sTy'
    let sTy ← instantiateMVars (← inferType s'E)
    let u ← getDecLevel sTy
    let elems := gs.getElems
    let v ← if elems.isEmpty then pure Level.zero else mkFreshLevelMVar
    let anyGetterTy := mkApp (mkConst ``Optic.AnyGetter [u, v]) sTy
    let getterExprs ← elems.mapM (elabAnyGetter sTy u v)
    let gsList ← mkListLit anyGetterTy getterExprs.toList
    return mkAppN (mkConst ``Optic.EqOnAll [u, v]) #[sTy, gsList, s'E, sE]

/-! ### Pretty-Printing Helpers and `@[app_unexpander]`s -/

/-- Strip outer parentheses from a syntax term. -/
private partial def stripParens (stx : Term) : Term :=
  match stx with
  | `(($t)) => stripParens t
  | _ => stx

/-- Check whether an identifier's macro-scope-erased name is in `names`. -/
private def isIdentOneOf (id : Ident) (names : List Name) : Bool :=
  let n := id.getId.eraseMacroScopes
  names.any (· == n)

/-- Check whether `stx` denotes `Optic.Lens.unit`. -/
private def isUnitLens (stx : Term) : Bool :=
  match stripParens stx with
  | `($id:ident) => isIdentOneOf id [`unit, `Lens.unit, `Optic.Lens.unit]
  | _ => false

/-- If `id` has the form `<Struct>.Lenses.<field>`, return `<field>`. -/
private def fieldLensName? (id : Ident) : Option Name :=
  let cs := id.getId.eraseMacroScopes.components
  if cs.length ≥ 2 && cs[cs.length - 2]! == `Lenses then
    some cs.getLast!
  else
    none

/-- Match a field projection `lhs.field` (`Lean.Parser.Term.proj`), returning `(lhs, fieldName)`. -/
private def matchProj? (stx : Term) : Option (Term × Name) :=
  match stx.raw with
  | .node _ `Lean.Parser.Term.proj #[lhs, _, field] =>
    if field.isIdent then some (⟨lhs⟩, field.getId.eraseMacroScopes) else none
  | _ => none

/-- Match a binary dot-method application `lhs.method rhs` (e.g. `l₁.comp l₂`, `l₁.prod l₂`). -/
private def matchDotApp? (stx : Term) (methodName : Name) : Option (Term × Term) :=
  match stripParens stx with
  | `($fn $rhs) =>
    match matchProj? fn with
    | some (lhs, field) => if field == methodName then some (lhs, rhs) else none
    | none => none
  | _ => none

/-- Match a lens composition `l₁ ∘ₗ l₂`, `l₁.comp l₂`, or `Lens.comp l₁ l₂`. -/
private def matchLensComp? (stx : Term) : Option (Term × Term) :=
  let stx := stripParens stx
  match stx with
  | `($l₁ ∘ₗ $l₂) => some (l₁, l₂)
  | `($f:ident $l₁ $l₂) =>
    if isIdentOneOf f [`Lens.comp, `Optic.Lens.comp] then some (l₁, l₂) else none
  | _ => matchDotApp? stx `comp

/-- Match a lens product `l₁ ×ₗ l₂`, `l₁.prod l₂`, or `Lens.prod l₁ l₂`. -/
private def matchLensProd? (stx : Term) : Option (Term × Term) :=
  let stx := stripParens stx
  match stx with
  | `($l₁ ×ₗ $l₂) => some (l₁, l₂)
  | `($f:ident $l₁ $l₂) =>
    if isIdentOneOf f [`Lens.prod, `Optic.Lens.prod] then some (l₁, l₂) else none
  | _ => matchDotApp? stx `prod

/-- Collapse a composition chain built solely from `<Struct>.Lenses.<field>` identifiers into a
compound dot-path `Name` (e.g. `` `data.regs.x0 ``). Returns `none` for any non-field lens. -/
private partial def lensDotPathName? (stx : Term) : Option Name := do
  let stx := stripParens stx
  if let some (l₁, l₂) := matchLensComp? stx then
    let p₁ ← lensDotPathName? l₁
    let p₂ ← lensDotPathName? l₂
    return p₁ ++ p₂
  match stx with
  | `($id:ident) => fieldLensName? id
  | _ => none

/-- Pretty-print a single lens term: collapses pure `StructName.Lenses.<field>` chains to dot-paths
and preserves all other lens expressions unchanged. -/
private def unexpandLensTerm (stx : Term) : Term :=
  match lensDotPathName? stx with
  | some pathName => mkIdent pathName
  | none => stripParens stx

/-- Flatten a `Lens.prod` tree into an array of pretty-printed lens terms (`Lens.unit` at top level
maps to `#[]`). -/
private partial def flattenProdLensAux (stx : Term) : Array Term :=
  let stx := stripParens stx
  if let some (l₁, l₂) := matchLensProd? stx then
    flattenProdLensAux l₁ ++ flattenProdLensAux l₂
  else
    #[unexpandLensTerm stx]

private def flattenProdLens (stx : Term) : Array Term :=
  if isUnitLens stx then #[] else flattenProdLensAux stx

/-- Strip `AnyGetter.*`, `ToAnyGetter.toAnyGetter`, `Lens.toGetter`, `Iso.toGetter`, and
`Getter.of` wrappers (including their structure-instance delaborations `{ α := …, getter := … }`
and `{ get := … }`) around a getter/view term. -/
private partial def stripGetterWrappers (stx : Term) : Term :=
  let stx := stripParens stx
  if let some (l, `toGetter) := matchProj? stx then
    stripGetterWrappers l
  else
    match stx with
    | `({ getter := $g }) => stripGetterWrappers g
    | `({ α := $_, getter := $g }) => stripGetterWrappers g
    | `({ get := $f }) => stripGetterWrappers f
    | `($f:ident $x) =>
      if isIdentOneOf f [
        `AnyGetter.of, `Optic.AnyGetter.of,
        `AnyGetter.ofLens, `Optic.AnyGetter.ofLens,
        `AnyGetter.ofFn, `Optic.AnyGetter.ofFn,
        `AnyGetter.ofIso, `Optic.AnyGetter.ofIso,
        `toAnyGetter, `ToAnyGetter.toAnyGetter, `Optic.ToAnyGetter.toAnyGetter,
        `Lens.toGetter, `Optic.Lens.toGetter,
        `Iso.toGetter, `Optic.Iso.toGetter,
        `Getter.of, `Optic.Getter.of
      ] then
        stripGetterWrappers x
      else
        stx
    | _ => stx

/-- Match an `AnyGetter.comp` / `Getter.comp` / `∘ᵍ` / `.comp` composition. -/
private def matchGetterComp? (stx : Term) : Option (Term × Term) :=
  let stx := stripParens stx
  match stx with
  | `($g₁ ∘ᵍ $g₂) => some (g₁, g₂)
  | `($f:ident $g₁ $g₂) =>
    if isIdentOneOf f [
      `AnyGetter.comp, `Optic.AnyGetter.comp,
      `Getter.comp, `Optic.Getter.comp
    ] then some (g₁, g₂) else none
  | _ => matchDotApp? stx `comp

/-- Pretty-print a single `EqOnAll` list element by stripping getter wrappers and collapsing
`StructName.Lenses.<field>` chains (and nested dot-path views like `data.regs.viewA`) to
dot-paths. -/
private def unexpandGetterTerm (stx : Term) : Term :=
  let core := stripGetterWrappers stx
  match lensDotPathName? core with
  | some pathName => mkIdent pathName
  | none =>
    match matchGetterComp? core with
    | some (outer, inner) =>
      let outer' := stripGetterWrappers outer
      let inner' := stripGetterWrappers inner
      match lensDotPathName? outer' with
      | some p₁ =>
        match lensDotPathName? inner' with
        | some p₂ => mkIdent (p₁ ++ p₂)
        | none =>
          match inner' with
          | `($id:ident) =>
            let cs := id.getId.eraseMacroScopes.components
            if cs.length ≥ 2 then
              mkIdent (p₁ ++ cs.getLast!)
            else
              core
          | _ => core
      | none => core
    | none => core

@[app_unexpander Optic.ReflTransGen]
def unexpandReflTransGenModifies : Unexpander
  | `($_ $rel $s' $s) => do
    match stripParens rel with
    | `($m:ident $l) =>
      unless isIdentOneOf m [`Modifies, `Optic.Modifies] do throw ()
      let ls := flattenProdLens l
      `($s' ≡ₚ $s except [$ls,*])
    | _ => throw ()
  | _ => throw ()

@[app_unexpander Optic.EqOnAll]
def unexpandEqOnAll : Unexpander
  | `($_ [$gs:term,*] $s' $s) => do
    let gs' := gs.getElems.map unexpandGetterTerm
    `($s' ≡ₚ $s on [$gs',*])
  | _ => throw ()

end Optic.Tactics.Notation

end
