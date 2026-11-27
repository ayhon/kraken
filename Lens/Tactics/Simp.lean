module

public import Lens.Basic
public import Lens.Frame
public import Lens.ProdFrame
public import Lens.Derive
public import Lens.ExtraNotation
public import Lens.Tactics.Disjoint
public import Lens.Tactics.SimpAttr
public meta import Lean

/-!
# Generic Optic Normalization Tactics (`lens_simp`, `lens_dsimp`)

Provides architecture-independent normalization for `Optic` (`Lens`, `Getter`, `Iso`) expressions:

- **`@[lens_simp]`**: extensible simp set pre-populated with core `Lens`, `Getter`, `Iso`, and
  `Optic.Notation` rewrite lemmas.
- **Disjointness- and independence-discharging simprocs (`Optic.Tactic`)**:
  - `k.get (l.set s v)` / `k.get (l.over f s)` (same lens, disjoint lenses, shared-prefix sub/super
    lenses, or independent getter),
  - `g.get (l.set s v)` / `g.get (l.over f s)` for arbitrary `Getter`s and derived views,
  - raw structure projections `S.field (l.set s v)`, `(l.set s v).i`, `Prod.fst`/`Prod.snd`,
    map lookups `m key`, and plain derived view functions `view (l.set s v)`,
  - `HasGet.getOf` / `Optic.Notation.viewOf` wrappers,
  - dead-overwrite and modifier collapse across disjoint intervening writes
    (`l.set (k₁.set (… (l.set s v₁) …) w₁) v₂ = k₁.set (… (l.set s v₂) …) w₁`, and similarly
    for `Lens.over`),
  - generalized `l.set s (l.get s) = s` even when `l` is compound or `l.get s` is written as a
    structure projection or notation wrapper.
- **`lens_simp [only]? [[lemmas,*]]? [at loc]?`**: runs the simplifier with `proj := false` so
  large structures and opaque user definitions are never exploded.
- **`lens_dsimp [at loc]?`**: targeted definitional reduction unfolding only optic combinators
  and `make_lenses` field lenses for structures mentioned in the target/location, yielding zero
  `Eq.trans` proof-term overhead on concrete struct-lens expressions.
-/

@[expose] public section

namespace Optic

universe u v w u₁

/-! ### Core `@[lens_simp]` Registrations -/

-- Notation wrappers unfolded definitionally (zero proof overhead):
attribute [lens_simp]
  Optic.Notation.pipe
  Optic.Notation.viewOf
  Optic.Notation.setOf
  Optic.Notation.overOf
  Optic.Lens.view

-- Core `Lens`, `Getter`, and `Iso` laws:
attribute [lens_simp]
  Optic.Lens.get_set
  Optic.Lens.set_get
  Optic.Lens.set_set
  Optic.Lens.over_id
  Optic.Lens.over_comp
  Optic.Lens.get_over
  Optic.Lens.set_over
  Optic.Lens.over_set
  Optic.Lens.comp_prod_set
  Optic.Getter.of_get
  Optic.Getter.id_get
  Optic.Getter.comp_get
  Optic.Getter.map_get
  Optic.Getter.prod_get
  Optic.Getter.const_get
  Optic.Iso.toLens_get
  Optic.Iso.toLens_set
  Optic.LawfulIso.inv_to
  Optic.LawfulIso.to_inv

/-! ### Helper Rewrite Lemmas for `lens_simp` & Simprocs -/

@[lens_simp ↓] theorem HasGet.getOf_lens {s : Type u} {a : Type v} (l : Lens s a) (x : s) :
    HasGet.getOf l x = l.get x := rfl

@[lens_simp ↓] theorem HasGet.getOf_getter {s : Type u} {a : Type v} (g : Getter s a) (x : s) :
    HasGet.getOf g x = g.get x := rfl

@[lens_simp ↓] theorem HasGet.getOf_iso {s : Type u} {a : Type v} (i : Iso s a) (x : s) :
    HasGet.getOf i x = i.to x := rfl

@[lens_simp ↓] theorem Lens.toGetter_get {s : Type u} {a : Type v} (l : Lens s a) (x : s) :
    l.toGetter.get x = l.get x := rfl

@[lens_simp ↓] theorem Iso.toGetter_get {s : Type u} {a : Type v} (i : Iso s a) (x : s) :
    i.toGetter.get x = i.to x := rfl

-- Helper theorems for `Iso` and primitive `Lens` combinators (dispatched syntactically via
-- `whnfOptic` in `lensSimpStep` rather than `@[lens_simp]`, because `Lens.id`/`Lens.unit`/
-- `Lens.fst`/`Lens.snd`/`Lens.prod`/`Iso.id` are `abbrev`s whose `Lens.mk`/`Iso.mk` patterns
-- would otherwise match arbitrary reducible lenses in `Simp`'s discrimination tree).
theorem Iso.id_to {s : Type u} (x : s) : Iso.id.to x = x := rfl
theorem Iso.id_inv {s : Type u} (x : s) : Iso.id.inv x = x := rfl

theorem Iso.symm_to {s : Type u} {a : Type v} (i : Iso s a) (x : a) :
    i.symm.to x = i.inv x := rfl

theorem Iso.symm_inv {s : Type u} {a : Type v} (i : Iso s a) (x : s) :
    i.symm.inv x = i.to x := rfl

theorem Iso.comp_to {s : Type u} {a : Type v} {b : Type w}
    (i₁ : Iso s a) (i₂ : Iso a b) (x : s) :
    (i₁.comp i₂).to x = i₂.to (i₁.to x) := rfl

theorem Iso.comp_inv {s : Type u} {a : Type v} {b : Type w}
    (i₁ : Iso s a) (i₂ : Iso a b) (y : b) :
    (i₁.comp i₂).inv y = i₁.inv (i₂.inv y) := rfl

theorem Lens.id_get {s : Type u} (x : s) : Lens.id.get x = x := rfl
theorem Lens.id_set {s : Type u} (x v : s) : Lens.id.set x v = v := rfl
theorem Lens.id_over {s : Type u} (f : s → s) (x : s) : Lens.id.over f x = f x := rfl

theorem Lens.unit_get {s : Type u} (x : s) :
    (Lens.unit.{u, v}).get x = PUnit.unit := rfl

theorem Lens.unit_set {s : Type u} (x : s) (v : PUnit.{v + 1}) :
    (Lens.unit.{u, v}).set x v = x := rfl

theorem Lens.unit_over {s : Type u} (f : PUnit.{v + 1} → PUnit.{v + 1}) (x : s) :
    (Lens.unit.{u, v}).over f x = x := rfl

theorem Lens.fst_get {a : Type u} {b : Type v} (p : a × b) :
    Lens.fst.get p = p.1 := rfl

theorem Lens.fst_set {a : Type u} {b : Type v} (p : a × b) (x : a) :
    Lens.fst.set p x = (x, p.2) := rfl

theorem Lens.snd_get {a : Type u} {b : Type v} (p : a × b) :
    Lens.snd.get p = p.2 := rfl

theorem Lens.snd_set {a : Type u} {b : Type v} (p : a × b) (y : b) :
    Lens.snd.set p y = (p.1, y) := rfl

theorem Lens.prod_get {s : Type u} {a : Type v} {b : Type w}
    (l₁ : Lens s a) (l₂ : Lens s b) (x : s) :
    (l₁.prod l₂).get x = (l₁.get x, l₂.get x) := rfl

theorem Lens.prod_set {s : Type u} {a : Type v} {b : Type w}
    (l₁ : Lens s a) (l₂ : Lens s b) (x : s) (p : a × b) :
    (l₁.prod l₂).set x p = l₂.set (l₁.set x p.1) p.2 := rfl

@[lens_simp] theorem Lens.atKey_get {k : Type u} {v : Type v} [DecidableEq k]
    (key : k) (f : k → v) :
    (Lens.atKey key).get f = f key := rfl

@[lens_simp] theorem Lens.over_id_fun {s : Type u} {a : Type v} (l : Lens s a) [LawfulLens l]
    (x : s) :
    l.over (fun y => y) x = x :=
  LawfulLens.set_get x

-- Pair projection & eta lemmas (needed because `lens_simp` runs with `proj := false`):
@[lens_simp] theorem prod_fst_mk {a : Type u} {b : Type v} (x : a) (y : b) : (x, y).1 = x := rfl
@[lens_simp] theorem prod_snd_mk {a : Type u} {b : Type v} (x : a) (y : b) : (x, y).2 = y := rfl
@[lens_simp] theorem prod_eta {a : Type u} {b : Type v} (p : a × b) : (p.1, p.2) = p := rfl

-- Composition helpers (not `@[lens_simp]` so `Lens.comp` stays intact for path-aware simprocs):
theorem Lens.comp_get {s : Type u} {a : Type v} {b : Type w}
    (outer : Lens s a) (inner : Lens a b) (x : s) :
    (outer.comp inner).get x = inner.get (outer.get x) := rfl

theorem Lens.comp_set {s : Type u} {a : Type v} {b : Type w}
    (outer : Lens s a) (inner : Lens a b) (x : s) (v : b) :
    (outer.comp inner).set x v = outer.set x (inner.set (outer.get x) v) := rfl

theorem Lens.get_comp_set {s : Type u} {a : Type v} {b : Type w}
    (outer : Lens s a) [LawfulLens outer] (inner : Lens a b) (x : s) (v : a) :
    (outer.comp inner).get (outer.set x v) = inner.get v := by
  change inner.get (outer.get (outer.set x v)) = inner.get v
  rw [Lens.get_set]

theorem Lens.get_set_comp {s : Type u} {a : Type v} {b : Type w}
    (outer : Lens s a) [LawfulLens outer] (inner : Lens a b) (x : s) (v : b) :
    outer.get ((outer.comp inner).set x v) = inner.set (outer.get x) v :=
  Lens.get_set outer x (inner.set (outer.get x) v)

theorem Lens.set_set_comp {s : Type u} {a : Type v} {b : Type w}
    (outer : Lens s a) [LawfulLens outer] (inner : Lens a b) (x : s) (v₁ : b) (v₂ : a) :
    outer.set ((outer.comp inner).set x v₁) v₂ = outer.set x v₂ :=
  Lens.set_set outer x (inner.set (outer.get x) v₁) v₂

theorem Lens.set_over_comp {s : Type u} {a : Type v} {b : Type w}
    (outer : Lens s a) [LawfulLens outer] (inner : Lens a b) (f : b → b) (x : s) (v₂ : a) :
    outer.set ((outer.comp inner).over f x) v₂ = outer.set x v₂ :=
  Lens.set_set outer x (inner.set (outer.get x) (f (inner.get (outer.get x)))) v₂

-- Disjointness & independence helpers for `Lens.over` and commutation:
theorem Disjoint.get₁_over₂ {s : Type u} {a : Type v} {b : Type w}
    {l₁ : Lens s a} {l₂ : Lens s b} [LawfulLens l₁] (h : Disjoint l₁ l₂)
    (x : s) (f : b → b) :
    l₁.get (l₂.over f x) = l₁.get x :=
  h.get₁_set₂ x (f (l₂.get x))

theorem Disjoint.get₂_over₁ {s : Type u} {a : Type v} {b : Type w}
    {l₁ : Lens s a} {l₂ : Lens s b} [LawfulLens l₂] (h : Disjoint l₁ l₂)
    (x : s) (f : a → a) :
    l₂.get (l₁.over f x) = l₂.get x :=
  h.get₂_set₁ x (f (l₁.get x))

theorem Disjoint.set_over_comm {s : Type u} {a : Type v} {b : Type w}
    {l₁ : Lens s a} {l₂ : Lens s b} [LawfulLens l₂] (h : Disjoint l₁ l₂)
    (x : s) (v₁ : a) (f₂ : b → b) :
    l₁.set (l₂.over f₂ x) v₁ = l₂.over f₂ (l₁.set x v₁) := by
  change l₁.set (l₂.set x (f₂ (l₂.get x))) v₁ =
    l₂.set (l₁.set x v₁) (f₂ (l₂.get (l₁.set x v₁)))
  rw [h.get₂_set₁, h.set_comm]

theorem Disjoint.over_set_comm {s : Type u} {a : Type v} {b : Type w}
    {l₁ : Lens s a} {l₂ : Lens s b} [LawfulLens l₁] (h : Disjoint l₁ l₂)
    (x : s) (f₁ : a → a) (v₂ : b) :
    l₁.over f₁ (l₂.set x v₂) = l₂.set (l₁.over f₁ x) v₂ := by
  change l₁.set (l₂.set x v₂) (f₁ (l₁.get (l₂.set x v₂))) =
    l₂.set (l₁.set x (f₁ (l₁.get x))) v₂
  rw [h.get₁_set₂, h.set_comm]

theorem Disjoint.over_over_comm {s : Type u} {a : Type v} {b : Type w}
    {l₁ : Lens s a} {l₂ : Lens s b} [LawfulLens l₁] [LawfulLens l₂] (h : Disjoint l₁ l₂)
    (x : s) (f₁ : a → a) (f₂ : b → b) :
    l₁.over f₁ (l₂.over f₂ x) = l₂.over f₂ (l₁.over f₁ x) := by
  change l₁.set (l₂.over f₂ x) (f₁ (l₁.get (l₂.over f₂ x))) =
    l₂.over f₂ (l₁.set x (f₁ (l₁.get x)))
  rw [h.get₁_over₂, h.set_over_comm]

theorem Independent.get_over {s : Type u} {a : Type v} {b : Type w}
    {l : Lens s a} {g : Getter s b} (h : Independent l g)
    (x : s) (f : a → a) :
    g.get (l.over f x) = g.get x :=
  h x (f (l.get x))

end Optic

end

public meta section

open Lean Meta Elab Tactic

namespace Optic.Tactic

/-! ### Meta Helpers for Optic Simprocs -/

/-- Run `x` under default transparency with projection reduction enabled, isolating optic reasoning
from `lens_simp`'s `proj := false` simplification configuration. -/
private def withLensMetaConfig {α : Type} (x : MetaM α) : MetaM α :=
  withDefault <| withConfig (fun c => { c with proj := .yesWithDelta }) x

/-- Check whether two lenses are definitionally equal up to reducible optic abbreviations,
projection reduction (associativity of `∘ₗ`), and `Lens.atKey` key equality, without unfolding
opaque user lenses. -/
private def lensesDefEq (l₁ l₂ : Expr) : MetaM Bool := withoutModifyingState do
  if l₁ == l₂ then return true
  withConfig (fun c => { c with proj := .yesWithDelta }) do
    if ← withReducible (isDefEq l₁ l₂) then return true
    let n₁ ← whnfOptic l₁
    let n₂ ← whnfOptic l₂
    if n₁.isAppOfArity ``Optic.Lens.atKey 4 && n₂.isAppOfArity ``Optic.Lens.atKey 4 then
      return ← isDefEq (n₁.getArg! 3) (n₂.getArg! 3)
    return false

/-- Check whether every segment of `prefixChain` is defeq to the leading segments of `fullChain`. -/
private def isChainPrefix (prefixChain fullChain : Array Expr) : MetaM Bool := do
  if prefixChain.isEmpty || fullChain.size <= prefixChain.size then return false
  for i in [0:prefixChain.size] do
    unless ← lensesDefEq prefixChain[i]! fullChain[i]! do
      return false
  return true

/-- Peel outermost `Optic.Notation.pipe`, `setOf`, `overOf` wrappers into `Lens.set` / `Lens.over`.
Every peeled step is definitionally equal (`rfl`) to the input. -/
private partial def peelUpdateNotation (e : Expr) : Expr :=
  let e := e.consumeMData
  if e.isAppOfArity ``Optic.Notation.pipe 4 then
    let x := e.getArg! 2
    let f := e.getArg! 3
    peelUpdateNotation (mkApp f x).headBeta
  else if e.isAppOfArity ``Optic.Notation.setOf 5 then
    let lvls := e.getAppFn.constLevels!
    mkAppN (mkConst ``Optic.Lens.set lvls)
      #[e.getArg! 0, e.getArg! 1, e.getArg! 2, e.getArg! 4, e.getArg! 3]
  else if e.isAppOfArity ``Optic.Notation.overOf 5 then
    let lvls := e.getAppFn.constLevels!
    mkAppN (mkConst ``Optic.Lens.over lvls)
      #[e.getArg! 0, e.getArg! 1, e.getArg! 2, e.getArg! 3, e.getArg! 4]
  else
    e

private inductive UpdateKind where
  | set (lens base val : Expr)
  | over (lens fn base : Expr)

private def matchUpdate? (u : Expr) : Option UpdateKind :=
  let u := peelUpdateNotation u
  if u.isAppOfArity ``Optic.Lens.set 5 then
    some (.set (u.getArg! 2) (u.getArg! 3) (u.getArg! 4))
  else if u.isAppOfArity ``Optic.Lens.over 5 then
    some (.over (u.getArg! 2) (u.getArg! 3) (u.getArg! 4))
  else
    none

/-- Build a `Simp.Result` after checking `prf : e = rhs` definitionally under `withLensMetaConfig`. -/
private def mkVerifiedResult? (e rhs prf : Expr) : MetaM (Option Simp.Result) := do
  let expected ← mkEq e rhs
  let prfTy ← inferType prf
  if ← withLensMetaConfig (withoutModifyingState <| isDefEq prfTy expected) then
    let prf' ← if prfTy == expected then pure prf else mkExpectedTypeHint prf expected
    return some { expr := rhs, proof? := some prf' }
  return none

/-- Try to simplify `k.get u` (where `e` is defeq to `k.get u` and `u` matches `upd`). -/
private def simplifyLensGetUpdate? (e k : Expr) (upd : UpdateKind) : MetaM (Option Simp.Result) := do
  match upd with
  | .set l base v =>
    -- 1. Same lens (`Lens.get_set`)
    if ← lensesDefEq k l then
      if (← synthLawfulLens? l).isSome then
        let prf ← mkAppM ``Optic.Lens.get_set #[l, base, v]
        return ← mkVerifiedResult? e v prf
    -- 2. Disjoint lenses (`Disjoint.get₂_set₁`)
    let kLawful? ← synthLawfulLens? k
    if kLawful?.isSome then
      if let some hDisj ← proveDisjoint? l k then
        let prf ← mkAppM ``Optic.Disjoint.get₂_set₁ #[hDisj, base, v]
        let rhs ← mkAppM ``Optic.Lens.get #[k, base]
        return ← mkVerifiedResult? e rhs prf
    -- 3. Shared-prefix sub/super lens (`get_comp_set`, `get_set_comp`)
    let kChain ← splitCompChain k
    let lChain ← splitCompChain l
    if ← isChainPrefix lChain kChain then
      if (← synthLawfulLens? l).isSome then
        let kTail ← mkCompChain (kChain.extract lChain.size kChain.size)
        let prf ← mkAppM ``Optic.Lens.get_comp_set #[l, kTail, base, v]
        let rhs ← mkAppM ``Optic.Lens.get #[kTail, v]
        return ← mkVerifiedResult? e rhs prf
    if ← isChainPrefix kChain lChain then
      if kLawful?.isSome then
        let lTail ← mkCompChain (lChain.extract kChain.size lChain.size)
        let prf ← mkAppM ``Optic.Lens.get_set_comp #[k, lTail, base, v]
        let kGetBase ← mkAppM ``Optic.Lens.get #[k, base]
        let rhs ← mkAppM ``Optic.Lens.set #[lTail, kGetBase, v]
        return ← mkVerifiedResult? e rhs prf
    -- 4. Independent fallback when `k` is not lawful (e.g., `@[lens_indep]` or local `Independent`)
    if kLawful?.isNone then
      let kGetter ← mkAppM ``Optic.Lens.toGetter #[k]
      if let some hInd ← proveIndependent? l kGetter then
        let prf := mkApp2 hInd base v
        let rhs ← mkAppM ``Optic.Lens.get #[k, base]
        return ← mkVerifiedResult? e rhs prf
    return none
  | .over l fn base =>
    -- 1. Same lens (`Lens.get_over`)
    if ← lensesDefEq k l then
      if (← synthLawfulLens? l).isSome then
        let prf ← mkAppM ``Optic.Lens.get_over #[l, fn, base]
        let kGetBase ← mkAppM ``Optic.Lens.get #[k, base]
        let rhs := mkApp fn kGetBase
        return ← mkVerifiedResult? e rhs prf
    -- 2. Disjoint lenses (`Disjoint.get₂_over₁`)
    let kLawful? ← synthLawfulLens? k
    if kLawful?.isSome then
      if let some hDisj ← proveDisjoint? l k then
        let prf ← mkAppM ``Optic.Disjoint.get₂_over₁ #[hDisj, base, fn]
        let rhs ← mkAppM ``Optic.Lens.get #[k, base]
        return ← mkVerifiedResult? e rhs prf
    -- 3. Independent fallback
    if kLawful?.isNone then
      let kGetter ← mkAppM ``Optic.Lens.toGetter #[k]
      if let some hInd ← proveIndependent? l kGetter then
        let prf ← mkAppM ``Optic.Independent.get_over #[hInd, base, fn]
        let rhs ← mkAppM ``Optic.Lens.get #[k, base]
        return ← mkVerifiedResult? e rhs prf
    return none

/-- Try to simplify `g.get u` for an arbitrary `Getter` `g` (including derived views). -/
private def simplifyGetterGetUpdate? (e g : Expr) (upd : UpdateKind) : MetaM (Option Simp.Result) := do
  let ng ← whnfOptic g
  if ng.isAppOfArity ``Optic.Lens.toGetter 3 then
    return ← simplifyLensGetUpdate? e (ng.getArg! 2) upd
  match upd with
  | .set l base v =>
    if let some hInd ← proveIndependent? l g then
      let prf := mkApp2 hInd base v
      let rhs ← mkAppM ``Optic.Getter.get #[g, base]
      return ← mkVerifiedResult? e rhs prf
    return none
  | .over l fn base =>
    if let some hInd ← proveIndependent? l g then
      let prf ← mkAppM ``Optic.Independent.get_over #[hInd, base, fn]
      let rhs ← mkAppM ``Optic.Getter.get #[g, base]
      return ← mkVerifiedResult? e rhs prf
    return none

/-- Try to simplify `HasGet.getOf o u` or `Optic.Notation.viewOf u o`. -/
private def simplifyHasGetUpdate? (e o : Expr) (upd : UpdateKind) : MetaM (Option Simp.Result) := do
  let oTy ← whnf (← inferType o)
  if oTy.isAppOfArity ``Optic.Lens 2 then
    return ← simplifyLensGetUpdate? e o upd
  if oTy.isAppOfArity ``Optic.Getter 2 then
    return ← simplifyGetterGetUpdate? e o upd
  if oTy.isAppOfArity ``Optic.Iso 2 then
    let k ← mkAppM ``Optic.Iso.toLens #[o]
    return ← simplifyLensGetUpdate? e k upd
  return none

/-- An intervening write step recorded while commuting an outer write inward to cancel a dead write. -/
private inductive InterveningWrite where
  | set (lens val hDisj : Expr)
  | over (lens fn hDisj : Expr)

/-- Replay recorded intervening writes around a collapsed inner proof `hInner : outerOp inner = rhs`.
When `outerIsSet = true`, `outerOp x = l.set x outerArg`; otherwise `outerOp x = l.over outerArg x`. -/
private def replayCommutedSteps (outerArg : Expr) (outerIsSet : Bool)
    (steps : Array InterveningWrite) (innerStart rhsStart hStart : Expr) :
    MetaM (Expr × Expr) := do
  let sTy ← inferType innerStart
  let mut curIn := innerStart
  let mut curOut := rhsStart
  let mut curPrf := hStart
  for step in steps.reverse do
    match step with
    | .set k w hDisj =>
      let hComm ←
        if outerIsSet then
          mkAppM ``Optic.Disjoint.set_comm #[hDisj, curIn, outerArg, w]
        else
          mkAppM ``Optic.Disjoint.over_set_comm #[hDisj, curIn, outerArg, w]
      let ctxFn ← withLocalDeclD `z sTy fun z => do
        mkLambdaFVars #[z] (← mkAppM ``Optic.Lens.set #[k, z, w])
      let hCongr ← mkCongrArg ctxFn curPrf
      curPrf ← mkEqTrans hComm hCongr
      curIn ← mkAppM ``Optic.Lens.set #[k, curIn, w]
      curOut ← mkAppM ``Optic.Lens.set #[k, curOut, w]
    | .over k g hDisj =>
      let hComm ←
        if outerIsSet then
          mkAppM ``Optic.Disjoint.set_over_comm #[hDisj, curIn, outerArg, g]
        else
          mkAppM ``Optic.Disjoint.over_over_comm #[hDisj, curIn, outerArg, g]
      let ctxFn ← withLocalDeclD `z sTy fun z => do
        mkLambdaFVars #[z] (← mkAppM ``Optic.Lens.over #[k, g, z])
      let hCongr ← mkCongrArg ctxFn curPrf
      curPrf ← mkEqTrans hComm hCongr
      curIn ← mkAppM ``Optic.Lens.over #[k, g, curIn]
      curOut ← mkAppM ``Optic.Lens.over #[k, g, curOut]
  return (curOut, curPrf)

/-- Check whether `v` is definitionally `l.get target` (either via `Lens.get`/`Lens.view` or a
projection / map-lookup path out of `target` whose reconstructed lens is defeq to `l`). -/
private def isGetOfLensOn (l target v : Expr) : MetaM Bool := do
  let vClean := v.consumeMData
  if vClean.isAppOfArity ``Optic.Lens.get 4 || vClean.isAppOfArity ``Optic.Lens.view 4 then
    let k := vClean.getArg! 2
    let base := vClean.getArg! 3
    if (← withoutModifyingState <| isDefEq base target) && (← lensesDefEq k l) then
      return true
  let abs ← kabstract vClean target
  if abs.hasLooseBVar 0 then
    let sTy ← inferType target
    return ← withLocalDeclD `s sTy fun sVar => do
      let body := abs.instantiate1 sVar
      let some k ← lensPathFromProj? sVar body | return false
      lensesDefEq k l
  return false

/-- Try to simplify `l.set inner v₂` by:
1. generalized `set_get` (including compound lenses, notation wrappers, struct projections, and
   restoring `l.get base` across disjoint intervening writes),
2. collapsing a dead inner `l.set`/`l.over` (or sub-lens write `(l ∘ₗ kTail).set`/`over`) across
   zero or more disjoint intervening writes. -/
private def simplifySet? (e l inner v₂ : Expr) : MetaM (Option Simp.Result) := do
  let some _ ← synthLawfulLens? l | return none

  -- 1. Direct generalized `set_get`: `l.set inner (l.get inner)` / `l.set inner inner.proj`
  if ← isGetOfLensOn l inner v₂ then
    let prf ← mkAppM ``Optic.Lens.set_get #[l, inner]
    if let some res ← mkVerifiedResult? e inner prf then
      return some res

  -- 2. Walk inward across disjoint intervening writes for overwrite collapse or restored `set_get`
  let lChain ← splitCompChain l
  let mut cur := inner
  let mut steps : Array InterveningWrite := #[]
  let maxDepth := 32
  for _ in [0:maxDepth] do
    let some upd := matchUpdate? cur | break
    match upd with
    | .set k base v₁ =>
      if ← lensesDefEq k l then
        let basePrf ← mkAppM ``Optic.Lens.set_set #[l, base, v₁, v₂]
        let baseRhs ← mkAppM ``Optic.Lens.set #[l, base, v₂]
        let innerStart ← mkAppM ``Optic.Lens.set #[l, base, v₁]
        let (finalRhs, finalPrf) ←
          replayCommutedSteps v₂ (outerIsSet := true) steps innerStart baseRhs basePrf
        return ← mkVerifiedResult? e finalRhs finalPrf
      let kChain ← splitCompChain k
      if ← isChainPrefix lChain kChain then
        let kTail ← mkCompChain (kChain.extract lChain.size kChain.size)
        let basePrf ← mkAppM ``Optic.Lens.set_set_comp #[l, kTail, base, v₁, v₂]
        let baseRhs ← mkAppM ``Optic.Lens.set #[l, base, v₂]
        let compLens ← mkAppM ``Optic.Lens.comp #[l, kTail]
        let innerStart ← mkAppM ``Optic.Lens.set #[compLens, base, v₁]
        let (finalRhs, finalPrf) ←
          replayCommutedSteps v₂ (outerIsSet := true) steps innerStart baseRhs basePrf
        return ← mkVerifiedResult? e finalRhs finalPrf
      if let some hDisj ← proveDisjoint? l k then
        steps := steps.push (.set k v₁ hDisj)
        cur := base
        if ← isGetOfLensOn l cur v₂ then
          let basePrf ← mkAppM ``Optic.Lens.set_get #[l, cur]
          let (finalRhs, finalPrf) ←
            replayCommutedSteps v₂ (outerIsSet := true) steps cur cur basePrf
          return ← mkVerifiedResult? e finalRhs finalPrf
      else
        break
    | .over k f₁ base =>
      if ← lensesDefEq k l then
        let basePrf ← mkAppM ``Optic.Lens.set_over #[l, f₁, base, v₂]
        let baseRhs ← mkAppM ``Optic.Lens.set #[l, base, v₂]
        let innerStart ← mkAppM ``Optic.Lens.over #[l, f₁, base]
        let (finalRhs, finalPrf) ←
          replayCommutedSteps v₂ (outerIsSet := true) steps innerStart baseRhs basePrf
        return ← mkVerifiedResult? e finalRhs finalPrf
      let kChain ← splitCompChain k
      if ← isChainPrefix lChain kChain then
        let kTail ← mkCompChain (kChain.extract lChain.size kChain.size)
        let basePrf ← mkAppM ``Optic.Lens.set_over_comp #[l, kTail, f₁, base, v₂]
        let baseRhs ← mkAppM ``Optic.Lens.set #[l, base, v₂]
        let compLens ← mkAppM ``Optic.Lens.comp #[l, kTail]
        let innerStart ← mkAppM ``Optic.Lens.over #[compLens, f₁, base]
        let (finalRhs, finalPrf) ←
          replayCommutedSteps v₂ (outerIsSet := true) steps innerStart baseRhs basePrf
        return ← mkVerifiedResult? e finalRhs finalPrf
      if (← synthLawfulLens? k).isSome then
        if let some hDisj ← proveDisjoint? l k then
          steps := steps.push (.over k f₁ hDisj)
          cur := base
          if ← isGetOfLensOn l cur v₂ then
            let basePrf ← mkAppM ``Optic.Lens.set_get #[l, cur]
            let (finalRhs, finalPrf) ←
              replayCommutedSteps v₂ (outerIsSet := true) steps cur cur basePrf
            return ← mkVerifiedResult? e finalRhs finalPrf
        else
          break
      else
        break
  return none

/-- Try to simplify `l.over f₂ inner` by identity elimination or merging into an inner `l.set` /
`l.over` across zero or more disjoint intervening writes. -/
private def simplifyOver? (e l f₂ inner : Expr) : MetaM (Option Simp.Result) := do
  let some _ ← synthLawfulLens? l | return none
  let f₂Clean := f₂.consumeMData
  if f₂Clean.isAppOf ``_root_.id || (match f₂Clean with | .lam _ _ (.bvar 0) _ => true | _ => false) then
    let prf ← mkAppM ``Optic.Lens.set_get #[l, inner]
    if let some res ← mkVerifiedResult? e inner prf then
      return some res

  let mut cur := inner
  let mut steps : Array InterveningWrite := #[]
  let maxDepth := 32
  for _ in [0:maxDepth] do
    let some upd := matchUpdate? cur | break
    match upd with
    | .set k base v₁ =>
      if ← lensesDefEq k l then
        let basePrf ← mkAppM ``Optic.Lens.over_set #[l, f₂, base, v₁]
        let baseRhs ← mkAppM ``Optic.Lens.set #[l, base, (mkApp f₂ v₁).headBeta]
        let innerStart ← mkAppM ``Optic.Lens.set #[l, base, v₁]
        let (finalRhs, finalPrf) ←
          replayCommutedSteps f₂ (outerIsSet := false) steps innerStart baseRhs basePrf
        return ← mkVerifiedResult? e finalRhs finalPrf
      if let some hDisj ← proveDisjoint? l k then
        steps := steps.push (.set k v₁ hDisj)
        cur := base
      else
        break
    | .over k f₁ base =>
      if ← lensesDefEq k l then
        let basePrf ← mkAppM ``Optic.Lens.over_comp #[l, f₁, f₂, base]
        let compFn ← mkAppM ``Function.comp #[f₂, f₁]
        let baseRhs ← mkAppM ``Optic.Lens.over #[l, compFn, base]
        let innerStart ← mkAppM ``Optic.Lens.over #[l, f₁, base]
        let (finalRhs, finalPrf) ←
          replayCommutedSteps f₂ (outerIsSet := false) steps innerStart baseRhs basePrf
        return ← mkVerifiedResult? e finalRhs finalPrf
      if (← synthLawfulLens? k).isSome then
        if let some hDisj ← proveDisjoint? l k then
          steps := steps.push (.over k f₁ hDisj)
          cur := base
        else
          break
      else
        break
  return none

/-- Walk a projection / map-lookup spine (`x.i`, `S.field x`, `p.1`, `p.2`, `m key`) looking for
an underlying `Lens.set` or `Lens.over` update at the root of the spine. -/
private partial def findProjSpineUpdate? (e : Expr) : MetaM (Option Expr) := do
  let e := e.consumeMData
  if (matchUpdate? e).isSome then
    return some e
  if let .proj _ _ base := e then
    return ← findProjSpineUpdate? base
  if e.isAppOfArity ``Prod.fst 3 || e.isAppOfArity ``Prod.snd 3 then
    return ← findProjSpineUpdate? (e.getArg! 2)
  if let some c := e.getAppFn.constName? then
    if let some pinfo ← getProjectionFnInfo? c then
      let args := e.getAppArgs
      if args.size == pinfo.numParams + 1 then
        return ← findProjSpineUpdate? args[pinfo.numParams]!
  if let .app fn _ := e then
    let fnTy ← whnf (← inferType fn)
    if fnTy.isForall && !fnTy.bindingBody!.hasLooseBVars then
      if let some u ← findProjSpineUpdate? fn then
        return some u
  return none

/-- Constants that should not be treated as user-defined derived views in `simplifyDerivedView?`. -/
private def isIgnoredViewHead (c : Name) : Bool :=
  c == ``Optic.Lens.get || c == ``Optic.Lens.set || c == ``Optic.Lens.over ||
  c == ``Optic.Lens.view || c == ``Optic.Lens.modifyF || c == ``Optic.Lens.comp ||
  c == ``Optic.Lens.prod || c == ``Optic.Lens.toGetter ||
  c == ``Optic.Getter.get || c == ``Optic.Getter.of || c == ``Optic.Getter.comp ||
  c == ``Optic.Getter.map || c == ``Optic.Getter.prod || c == ``Optic.Getter.const ||
  c == ``Optic.Iso.to || c == ``Optic.Iso.inv || c == ``Optic.Iso.toLens ||
  c == ``Optic.Iso.toGetter || c == ``Optic.HasGet.getOf ||
  c == ``Optic.Notation.pipe || c == ``Optic.Notation.viewOf ||
  c == ``Optic.Notation.setOf || c == ``Optic.Notation.overOf ||
  c == ``_root_.id || c == ``Function.comp

/-- Try to simplify a raw structure projection / map lookup (`(l.set s v).data.regs.x0`,
`((l.set s v).data.dmem) a`) or a plain derived-view application (`stateViewA (l.set s v)`). -/
private def simplifyProjOrView? (e : Expr) : MetaM (Option Simp.Result) := do
  -- Part A: projection / map-lookup spine ending in a state update `u`
  if let some u ← findProjSpineUpdate? e then
    if u != e then
      if let some upd := matchUpdate? u then
        let abs ← kabstract e u
        if abs.hasLooseBVar 0 then
          let sTy ← inferType u
          let res? ← withLocalDeclD `s sTy fun sVar => do
            let body := abs.instantiate1 sVar
            let some k ← lensPathFromProj? sVar body | return none
            if (← whnfOptic k).isAppOfArity ``Optic.Lens.id 1 then
              return none
            match upd with
            | .set l base v =>
              if ← lensesDefEq k l then
                if (← synthLawfulLens? l).isSome then
                  let prf ← mkAppM ``Optic.Lens.get_set #[l, base, v]
                  return ← mkVerifiedResult? e v prf
              if (← synthLawfulLens? k).isSome then
                if let some hDisj ← proveDisjoint? l k then
                  let prf ← mkAppM ``Optic.Disjoint.get₂_set₁ #[hDisj, base, v]
                  let rhs := abs.instantiate1 base
                  return ← mkVerifiedResult? e rhs prf
              return none
            | .over l fn base =>
              if ← lensesDefEq k l then
                if (← synthLawfulLens? l).isSome then
                  let prf ← mkAppM ``Optic.Lens.get_over #[l, fn, base]
                  let rhs := (mkApp fn (abs.instantiate1 base)).headBeta
                  return ← mkVerifiedResult? e rhs prf
              if (← synthLawfulLens? k).isSome then
                if let some hDisj ← proveDisjoint? l k then
                  let prf ← mkAppM ``Optic.Disjoint.get₂_over₁ #[hDisj, base, fn]
                  let rhs := abs.instantiate1 base
                  return ← mkVerifiedResult? e rhs prf
              return none
          if res?.isSome then
            return res?

  -- Part B: plain derived-view function application `view … (l.set s v) …`
  if !e.isApp then return none
  let fn := e.getAppFn
  let some c := fn.constName? | return none
  if isIgnoredViewHead c then return none
  let some (.defnInfo _) := (← getEnv).find? c | return none
  if (← isProjectionFn c) || (← isMatcher c) || (← isInstance c) then return none
  let eTy ← inferType e
  if ← isProp e then return none
  let eLvl ← getLevel eTy
  if eLvl.isZero then return none

  let args := e.getAppArgs
  -- Walk arguments from last to first (most views take state as the final argument)
  for idx in [0:args.size] do
    let i := args.size - 1 - idx
    let arg := args[i]!
    let some upd := matchUpdate? arg | continue
    let sTy ← inferType arg
    let sLvl ← getLevel sTy
    if sLvl.isZero then continue
    let viewFn? : Option (Expr × (Expr → Expr)) ←
      if i == args.size - 1 then
        let appFn := e.appFn!
        let appFnTy ← whnf (← inferType appFn)
        if appFnTy.isForall && !appFnTy.bindingBody!.hasLooseBVars then
          pure (some (appFn, fun b => mkApp appFn b))
        else
          pure none
      else
        commitWhenSomeNoEx? do
          withLocalDeclD `s sTy fun sVar => do
            let body := mkAppN fn (args.set! i sVar)
            let bodyTy ← inferType body
            if bodyTy.containsFVar sVar.fvarId! then return none
            let lam ← mkLambdaFVars #[sVar] body
            return some (lam, fun b => mkAppN fn (args.set! i b))
    let some (viewFn, mkRhs) := viewFn? | continue
    let g ← mkAppM ``Optic.Getter.of #[viewFn]
    match upd with
    | .set l base v =>
      if let some hInd ← proveIndependent? l g then
        let prf := mkApp2 hInd base v
        let rhs := mkRhs base
        if let some res ← mkVerifiedResult? e rhs prf then
          return some res
    | .over l fnMod base =>
      if let some hInd ← proveIndependent? l g then
        let prf ← mkAppM ``Optic.Independent.get_over #[hInd, base, fnMod]
        let rhs := mkRhs base
        if let some res ← mkVerifiedResult? e rhs prf then
          return some res
  return none

/-- Normalize primitive `Lens` (`id`, `unit`, `fst`, `snd`, `prod`) and `Iso` (`id`, `symm`, `comp`)
combinators syntactically via `whnfOptic` without ever unfolding `make_lenses` or user lenses. -/
private def simplifyPrimOptic? (isPost : Bool) (e : Expr) : MetaM (Option Simp.Result) := do
  -- `Lens.get` / `Lens.view` on primitive lenses
  if e.isAppOfArity ``Optic.Lens.get 4 || e.isAppOfArity ``Optic.Lens.view 4 then
    let l ← whnfOptic (e.getArg! 2)
    let x := e.getArg! 3
    if l.isAppOfArity ``Optic.Lens.id 1 then
      return ← mkVerifiedResult? e x (← mkAppM ``Optic.Lens.id_get #[x])
    if l.isAppOfArity ``Optic.Lens.unit 1 then
      let prf ← mkAppOptM ``Optic.Lens.unit_get #[some (e.getArg! 0), some x]
      let rhs := (← inferType prf).appArg!
      return ← mkVerifiedResult? e rhs prf
    if l.isAppOfArity ``Optic.Lens.fst 2 then
      let rhs ← mkAppM ``Prod.fst #[x]
      return ← mkVerifiedResult? e rhs (← mkAppM ``Optic.Lens.fst_get #[x])
    if l.isAppOfArity ``Optic.Lens.snd 2 then
      let rhs ← mkAppM ``Prod.snd #[x]
      return ← mkVerifiedResult? e rhs (← mkAppM ``Optic.Lens.snd_get #[x])
    if isPost && l.isAppOfArity ``Optic.Lens.prod 5 then
      let l₁ := l.getArg! 3
      let l₂ := l.getArg! 4
      let rhs ← mkAppM ``Prod.mk #[← mkAppM ``Optic.Lens.get #[l₁, x], ← mkAppM ``Optic.Lens.get #[l₂, x]]
      return ← mkVerifiedResult? e rhs (← mkAppM ``Optic.Lens.prod_get #[l₁, l₂, x])
  -- `Lens.set` on primitive lenses
  if e.isAppOfArity ``Optic.Lens.set 5 then
    let l ← whnfOptic (e.getArg! 2)
    let x := e.getArg! 3
    let v := e.getArg! 4
    if l.isAppOfArity ``Optic.Lens.id 1 then
      return ← mkVerifiedResult? e v (← mkAppM ``Optic.Lens.id_set #[x, v])
    if l.isAppOfArity ``Optic.Lens.unit 1 then
      return ← mkVerifiedResult? e x (← mkAppM ``Optic.Lens.unit_set #[x, v])
    if l.isAppOfArity ``Optic.Lens.fst 2 then
      let rhs ← mkAppM ``Prod.mk #[v, ← mkAppM ``Prod.snd #[x]]
      return ← mkVerifiedResult? e rhs (← mkAppM ``Optic.Lens.fst_set #[x, v])
    if l.isAppOfArity ``Optic.Lens.snd 2 then
      let rhs ← mkAppM ``Prod.mk #[← mkAppM ``Prod.fst #[x], v]
      return ← mkVerifiedResult? e rhs (← mkAppM ``Optic.Lens.snd_set #[x, v])
    if isPost && l.isAppOfArity ``Optic.Lens.prod 5 then
      let l₁ := l.getArg! 3
      let l₂ := l.getArg! 4
      let v₁ ← mkAppM ``Prod.fst #[v]
      let v₂ ← mkAppM ``Prod.snd #[v]
      let inner ← mkAppM ``Optic.Lens.set #[l₁, x, v₁]
      let rhs ← mkAppM ``Optic.Lens.set #[l₂, inner, v₂]
      return ← mkVerifiedResult? e rhs (← mkAppM ``Optic.Lens.prod_set #[l₁, l₂, x, v])
  -- `Lens.over` on primitive lenses
  if e.isAppOfArity ``Optic.Lens.over 5 then
    let l ← whnfOptic (e.getArg! 2)
    let f := e.getArg! 3
    let x := e.getArg! 4
    if l.isAppOfArity ``Optic.Lens.id 1 then
      return ← mkVerifiedResult? e (mkApp f x).headBeta (← mkAppM ``Optic.Lens.id_over #[f, x])
    if l.isAppOfArity ``Optic.Lens.unit 1 then
      return ← mkVerifiedResult? e x (← mkAppM ``Optic.Lens.unit_over #[f, x])
  -- `Iso.to` / `Iso.inv` on primitive isos
  if e.isAppOfArity ``Optic.Iso.to 4 then
    let i ← whnfOptic (e.getArg! 2)
    let x := e.getArg! 3
    if i.isAppOfArity ``Optic.Iso.id 1 then
      return ← mkVerifiedResult? e x (← mkAppM ``Optic.Iso.id_to #[x])
    if i.isAppOfArity ``Optic.Iso.symm 3 then
      let i₀ := i.getArg! 2
      let rhs ← mkAppM ``Optic.Iso.inv #[i₀, x]
      return ← mkVerifiedResult? e rhs (← mkAppM ``Optic.Iso.symm_to #[i₀, x])
    if i.isAppOfArity ``Optic.Iso.comp 5 then
      let i₁ := i.getArg! 3
      let i₂ := i.getArg! 4
      let rhs ← mkAppM ``Optic.Iso.to #[i₂, ← mkAppM ``Optic.Iso.to #[i₁, x]]
      return ← mkVerifiedResult? e rhs (← mkAppM ``Optic.Iso.comp_to #[i₁, i₂, x])
  if e.isAppOfArity ``Optic.Iso.inv 4 then
    let i ← whnfOptic (e.getArg! 2)
    let y := e.getArg! 3
    if i.isAppOfArity ``Optic.Iso.id 1 then
      return ← mkVerifiedResult? e y (← mkAppM ``Optic.Iso.id_inv #[y])
    if i.isAppOfArity ``Optic.Iso.symm 3 then
      let i₀ := i.getArg! 2
      let rhs ← mkAppM ``Optic.Iso.to #[i₀, y]
      return ← mkVerifiedResult? e rhs (← mkAppM ``Optic.Iso.symm_inv #[i₀, y])
    if i.isAppOfArity ``Optic.Iso.comp 5 then
      let i₁ := i.getArg! 3
      let i₂ := i.getArg! 4
      let rhs ← mkAppM ``Optic.Iso.inv #[i₁, ← mkAppM ``Optic.Iso.inv #[i₂, y]]
      return ← mkVerifiedResult? e rhs (← mkAppM ``Optic.Iso.comp_inv #[i₁, i₂, y])
  return none

/-- Core optic normalization step used by both `lensPreSimproc` and `lensPostSimproc`. -/
private def lensSimpStep (isPost : Bool) (e : Expr) : SimpM Simp.Step := do
  let e := e.consumeMData
  let res? ← withLensMetaConfig do
    -- 1. `Lens.get` / `Lens.view`
    if e.isAppOfArity ``Optic.Lens.get 4 || e.isAppOfArity ``Optic.Lens.view 4 then
      if let some upd := matchUpdate? (e.getArg! 3) then
        if let some res ← simplifyLensGetUpdate? e (e.getArg! 2) upd then
          return some res
    -- 2. `Getter.get`
    if e.isAppOfArity ``Optic.Getter.get 4 then
      if let some upd := matchUpdate? (e.getArg! 3) then
        if let some res ← simplifyGetterGetUpdate? e (e.getArg! 2) upd then
          return some res
    -- 3. `HasGet.getOf` / `Optic.Notation.viewOf`
    if e.isAppOfArity ``Optic.HasGet.getOf 6 then
      if let some upd := matchUpdate? (e.getArg! 5) then
        if let some res ← simplifyHasGetUpdate? e (e.getArg! 4) upd then
          return some res
    if e.isAppOfArity ``Optic.Notation.viewOf 6 then
      if let some upd := matchUpdate? (e.getArg! 4) then
        if let some res ← simplifyHasGetUpdate? e (e.getArg! 5) upd then
          return some res
    -- 4. `Lens.set` / `Lens.over` (including notation wrappers)
    if let some upd := matchUpdate? e then
      match upd with
      | .set l base v =>
        if let some res ← simplifySet? e l base v then
          return some res
      | .over l fn base =>
        if let some res ← simplifyOver? e l fn base then
          return some res
    -- 5. Primitive optic combinators (`Lens.id`/`unit`/`fst`/`snd`/`prod`, `Iso.id`/`symm`/`comp`)
    if let some res ← simplifyPrimOptic? isPost e then
      return some res
    -- 6. Raw projections, map lookups, and plain derived views
    if let some res ← simplifyProjOrView? e then
      return some res
    -- 7. In post-order, close equalities `lhs = rhs` that are reducible+instances+proj defeq
    --    (e.g. `stX0.get st = st.data.regs.x0`) without unfolding opaque definitions
    if isPost then
      if let some (_, lhs, rhs) := e.eq? then
        let defEq ← withoutModifyingState <|
          withReducibleAndInstances <| withConfig (fun c => { c with proj := .yesWithDelta }) <|
            isDefEq lhs rhs
        if defEq then
          let reflPrf ← mkEqRefl lhs
          let eqTruePrf ← mkAppM ``eq_true #[reflPrf]
          if let some res ← mkVerifiedResult? e (mkConst ``True) eqTruePrf then
            return some res
    return none
  match res? with
  | some r => return .visit r
  | none => return .continue

/-- Pre-order optic simproc: prunes dead reads/subterms top-down before descending. -/
def lensPreSimproc : Simp.Simproc := lensSimpStep (isPost := false)

/-- Post-order optic simproc: fires after child simplification and user-supplied rewrite lemmas. -/
def lensPostSimproc : Simp.Simproc := lensSimpStep (isPost := true)

/-- Discharger for `lens_simp`: discharges `Optic.Disjoint`, `Optic.Independent`, and `Ne`
side conditions automatically, falling back to `Simp.dischargeDefault?`. -/
def lensDischarge? (e : Expr) : SimpM (Option Expr) := do
  let e ← instantiateMVars e
  let e' := e.consumeMData
  let prf? ← withLensMetaConfig do
    if e'.isAppOfArity ``Optic.Disjoint 5 then
      proveDisjoint? (e'.getArg! 3) (e'.getArg! 4)
    else if e'.isAppOfArity ``Optic.Independent 5 then
      proveIndependent? (e'.getArg! 3) (e'.getArg! 4)
    else if e'.isAppOfArity ``Ne 3 then
      proveNe? (e'.getArg! 1) (e'.getArg! 2)
    else
      return none
  if prf?.isSome then
    return prf?
  Simp.dischargeDefault? e

/-- Build `Simp.Methods` combining `lensPreSimproc`, `lensPostSimproc`, `lensDischarge?`, and
any user-provided simprocs. -/
def mkLensSimpMethods (simprocs : Simp.SimprocsArray := #[]) : Simp.Methods := {
  pre := lensPreSimproc >> Simp.preDefault simprocs
  post := lensPostSimproc >> Simp.postDefault simprocs
  dpre := Simp.dpreDefault simprocs
  dpost := Simp.dpostDefault simprocs
  discharge? := lensDischarge?
  wellBehavedDischarge := false
}

/-- Simplify `mvarId` (selected hypotheses and/or target) using custom `Simp.Methods`. -/
def lensSimpGoal (mvarId : MVarId) (ctx : Simp.Context) (methods : Simp.Methods)
    (simplifyTarget : Bool := true) (fvarIdsToSimp : Array FVarId := #[]) :
    MetaM (Option (Array FVarId × MVarId)) := do
  mvarId.withContext do
    mvarId.checkNotAssigned `lens_simp
    let mut mvarIdNew := mvarId
    let mut toAssert := #[]
    let mut replaced := #[]
    let mut stats : Simp.Stats := {}
    for fvarId in fvarIdsToSimp do
      let localDecl ← fvarId.getDecl
      let type ← instantiateMVars localDecl.type
      let ctxHyp := ctx.setSimpTheorems <| ctx.simpTheorems.eraseTheorem (.fvar localDecl.fvarId)
      let (r, stats') ← Simp.main type ctxHyp stats methods
      stats := stats'
      match r.proof? with
      | some _ =>
        match ← applySimpResult mvarIdNew (mkFVar fvarId) type r with
        | none => return none
        | some (value, typeNew) =>
          toAssert := toAssert.push { userName := localDecl.userName, type := typeNew, value }
      | none =>
        if r.expr.isFalse then
          mvarIdNew.assign (← mkFalseElim (← mvarIdNew.getType) (mkFVar fvarId))
          return none
        mvarIdNew ← mvarIdNew.replaceLocalDeclDefEq fvarId r.expr
        replaced := replaced.push fvarId
    if simplifyTarget then
      let target ← instantiateMVars (← mvarIdNew.getType)
      let (r, _) ← Simp.main target ctx stats methods
      if r.expr.isTrue then
        match r.proof? with
        | some proof => mvarIdNew.assign (← mkOfEqTrue proof)
        | none => mvarIdNew.assign (mkConst ``True.intro)
        return none
      else
        mvarIdNew ← applySimpResultToTarget mvarIdNew target r
    let (fvarIdsNew, mvarIdNew') ← mvarIdNew.assertHypotheses toAssert
    mvarIdNew := mvarIdNew'
    let toClear := fvarIdsToSimp.filter fun fvarId => !replaced.contains fvarId
    mvarIdNew ← mvarIdNew.tryClearMany toClear
    if ctx.config.failIfUnchanged && mvarId == mvarIdNew then
      throwError "`lens_simp` made no progress"
    return some (fvarIdsNew, mvarIdNew)

/-! ### Targeted Definitional Reduction (`lens_dsimp`) -/

/-- Optic combinators unfolded by `lens_dsimp`. -/
private def lensDSimpCombinators : Array Name := #[
  ``Optic.Notation.pipe,
  ``Optic.Notation.viewOf,
  ``Optic.Notation.setOf,
  ``Optic.Notation.overOf,
  ``Optic.HasGet.getOf,
  ``Optic.Lens.view,
  ``Optic.Lens.over,
  ``Optic.Lens.comp,
  ``Optic.Lens.prod,
  ``Optic.Lens.id,
  ``Optic.Lens.unit,
  ``Optic.Lens.fst,
  ``Optic.Lens.snd,
  ``Optic.Lens.toGetter,
  ``Optic.Getter.id,
  ``Optic.Getter.comp,
  ``Optic.Getter.map,
  ``Optic.Getter.prod,
  ``Optic.Getter.const,
  ``Optic.Iso.id,
  ``Optic.Iso.symm,
  ``Optic.Iso.comp,
  ``Optic.Iso.toGetter,
  ``Optic.Iso.toLens
]

/-- Collect all structure names relevant to `exprs` (directly mentioned structures, structures of
`make_lenses` lenses, structures occurring in types of free variables, and transitively nested
structure field types), then return all `make_lenses` field lens names for those structures. -/
private def collectRelevantFieldLenses (exprs : Array Expr) : MetaM (Array Name) := do
  let env ← getEnv
  let mut structWorklist : Array Name := #[]
  let mut visitedStructs : NameSet := {}
  let mut lensNames : NameSet := {}

  let recordConst (c : Name) (work : Array Name) (vis : NameSet) (lenses : NameSet) :
      Array Name × NameSet × NameSet :=
    let (work, vis, lenses) :=
      if let some info := Optic.Derive.lookupLensField? env c then
        let lenses := lenses.insert info.lensName
        if vis.contains info.structName then (work, vis, lenses)
        else (work.push info.structName, vis.insert info.structName, lenses)
      else (work, vis, lenses)
    if isStructure env c && !vis.contains c then
      (work.push c, vis.insert c, lenses)
    else
      (work, vis, lenses)

  let scanExpr (e : Expr) (work : Array Name) (vis : NameSet) (lenses : NameSet) :
      Array Name × NameSet × NameSet :=
    e.getUsedConstants.foldl (init := (work, vis, lenses)) fun (w, v, l) c =>
      recordConst c w v l

  for e in exprs do
    let e ← instantiateMVars e
    (structWorklist, visitedStructs, lensNames) :=
      scanExpr e structWorklist visitedStructs lensNames
    let fvars := (collectFVars {} e).fvarIds
    for fv in fvars do
      if let some decl := (← getLCtx).find? fv then
        let dTy ← instantiateMVars decl.type
        (structWorklist, visitedStructs, lensNames) :=
          scanExpr dTy structWorklist visitedStructs lensNames
        if let some dVal := decl.value? then
          let dVal ← instantiateMVars dVal
          (structWorklist, visitedStructs, lensNames) :=
            scanExpr dVal structWorklist visitedStructs lensNames

  -- Transitively follow structure field types (e.g. `MiniState` -> `MiniMachineData` -> `MiniRegs`)
  let mut idx := 0
  while idx < structWorklist.size do
    let sName := structWorklist[idx]!
    idx := idx + 1
    if let some sInfo := getStructureInfo? env sName then
      for i in [0:sInfo.fieldNames.size] do
        if let some info := Optic.Derive.lookupStructFieldLens? env sName i then
          lensNames := lensNames.insert info.lensName
      let ctorName := getStructureCtor env sName |>.name
      if let some ctorInfo := env.find? ctorName then
        (structWorklist, visitedStructs, lensNames) :=
          scanExpr ctorInfo.type structWorklist visitedStructs lensNames

  return lensNames.toArray

/-- Build the targeted `Simp.Context` for `lens_dsimp` over `exprs`. -/
private def mkLensDSimpContext (exprs : Array Expr) : MetaM Simp.Context := do
  let mut thms : SimpTheorems := {}
  for c in lensDSimpCombinators do
    thms := thms.addDeclToUnfoldCore c
  -- Rfl theorems for `HasGet.getOf` so `st ^. l` reduces definitionally to `l.get st`:
  for rflThm in #[``Optic.HasGet.getOf_lens, ``Optic.HasGet.getOf_getter, ``Optic.HasGet.getOf_iso] do
    thms ← thms.addConst rflThm
  let fieldLenses ← collectRelevantFieldLenses exprs
  for fl in fieldLenses do
    thms := thms.addDeclToUnfoldCore fl
  let congrTheorems ← getSimpCongrTheorems
  Simp.mkContext
    (config := { dsimp := true, proj := true, beta := true, iota := true, zeta := true, failIfUnchanged := true })
    (simpTheorems := #[thms])
    (congrTheorems := congrTheorems)

/-- Run targeted definitional reduction on `mvarId` without auto-closing equalities, so both
`lens_dsimp; rfl` and `lens_dsimp at h` work cleanly with pure definitional equality. -/
def lensDSimpGoal (mvarId : MVarId) (simplifyTarget : Bool := true)
    (fvarIdsToSimp : Array FVarId := #[]) : MetaM (Option MVarId) := do
  mvarId.withContext do
    mvarId.checkNotAssigned `lens_dsimp
    let mut exprs : Array Expr := #[]
    for fv in fvarIdsToSimp do
      exprs := exprs.push (← instantiateMVars (← fv.getType))
    if simplifyTarget then
      exprs := exprs.push (← instantiateMVars (← mvarId.getType))
    let ctx ← mkLensDSimpContext exprs
    let mut mvarIdNew := mvarId
    let mut stats : Simp.Stats := {}
    for fv in fvarIdsToSimp do
      let type ← instantiateMVars (← fv.getType)
      let (typeNew, stats') ← Meta.dsimp type ctx #[] stats
      stats := stats'
      if typeNew.isFalse then
        mvarIdNew.assign (← mkFalseElim (← mvarIdNew.getType) (mkFVar fv))
        return none
      if typeNew != type then
        mvarIdNew ← mvarIdNew.replaceLocalDeclDefEq fv typeNew
    if simplifyTarget then
      let target ← instantiateMVars (← mvarIdNew.getType)
      let (targetNew, _) ← Meta.dsimp target ctx #[] stats
      if targetNew.isTrue then
        mvarIdNew.assign (mkConst ``True.intro)
        return none
      if targetNew != target then
        mvarIdNew ← mvarIdNew.replaceTargetDefEq targetNew
    if mvarId == mvarIdNew then
      throwError "`lens_dsimp` made no progress"
    return some mvarIdNew

/-! ### User-Facing Tactics (`lens_simp`, `lens_dsimp`) -/

/-- Normalize optic expressions using `@[lens_simp]` lemmas, disjointness/independence-discharging
simprocs, and dead-overwrite collapse, without unfolding opaque user definitions or exploding
large structures. -/
syntax (name := lensSimpTac)
  "lens_simp" (" only")? (Lean.Parser.Tactic.simpArgs)? (Lean.Parser.Tactic.location)? : tactic

/-- Unwrap optic notation (`&`, `^.`, `.~`, `%~`, `HasGet.getOf`, `Lens.view`) inside user-supplied
`lens_simp [...]` theorems via definitional `dsimp` (`proj := false`) so hypotheses like
`h : (st ^. stX0) = 5` also match normalized `stX0.get st` terms. -/
private def addNormalizedUserSimpArgs (ctx : Simp.Context)
    (simpArgs : Array (Syntax × ElabSimpArgResult)) : MetaM Simp.Context := do
  let mut normThms : SimpTheorems := {}
  for c in #[``Optic.Notation.pipe, ``Optic.Notation.viewOf, ``Optic.Notation.setOf,
      ``Optic.Notation.overOf, ``Optic.Lens.view] do
    normThms := normThms.addDeclToUnfoldCore c
  for rflThm in #[``Optic.HasGet.getOf_lens, ``Optic.HasGet.getOf_getter, ``Optic.HasGet.getOf_iso] do
    normThms ← normThms.addConst rflThm
  let congrTheorems ← getSimpCongrTheorems
  let normCtx ← Simp.mkContext
    (config := { dsimp := true, proj := false, beta := true, iota := false, zeta := false })
    (simpTheorems := #[normThms])
    (congrTheorems := congrTheorems)
  let mut thmsArray := ctx.simpTheorems
  let mut thms := thmsArray[0]!
  let normalizeProof (origin : Origin) (levelParams : Array Name) (proof : Expr) (post : Bool)
      (curThms : SimpTheorems) : MetaM SimpTheorems := do
    if proof.isConst then return curThms
    try
      let ty ← instantiateMVars (← inferType proof)
      let (tyNew, _) ← Meta.dsimp ty normCtx #[]
      if tyNew != ty then
        let normProof ← mkExpectedTypeHint proof tyNew
        let extraThms ← mkSimpTheoremFromExpr origin levelParams normProof
          (post := post) (inv := false) (config := ctx.indexConfig)
        let mut out := curThms
        for et in extraThms do
          out := out.addSimpEntry (.thm et)
        return out
      return curThms
    catch _ =>
      return curThms

  let mut hasStar := false
  for (_, arg) in simpArgs do
    if arg matches .star then
      hasStar := true
    for simpThm in arg.simpTheorems do
      thms ← normalizeProof simpThm.origin simpThm.levelParams simpThm.proof simpThm.post thms
  if hasStar then
    for fv in (← getPropHyps) do
      unless ctx.simpTheorems.isErased (.fvar fv) do
        thms ← normalizeProof (.fvar fv) #[] (mkFVar fv) (post := true) thms
  return ctx.setSimpTheorems (thmsArray.set! 0 thms)

@[tactic lensSimpTac]
def evalLensSimp : Tactic := fun stx => withMainContext do
  let isOnly := !stx[1].isNone
  let argsStx := if stx[2].isNone then stx[2] else stx[2][0]
  let loc := expandOptLocation stx[3]
  let mut baseThms : SimpTheorems ←
    if isOnly then
      let mut t ← simpOnlyBuiltins.foldlM (·.addConst ·) ({} : SimpTheorems)
      for c in #[``Optic.Notation.pipe, ``Optic.Notation.viewOf, ``Optic.Notation.setOf,
          ``Optic.Notation.overOf, ``Optic.Lens.view] do
        t := t.addDeclToUnfoldCore c
      pure t
    else
      let mut t ← lensSimpExt.getTheorems
      for b in simpOnlyBuiltins do
        t ← t.addConst b
      pure t
  let congrTheorems ← getSimpCongrTheorems
  let initCtx ← Simp.mkContext
    (config := { proj := false, failIfUnchanged := true })
    (simpTheorems := #[baseThms])
    (congrTheorems := congrTheorems)
  let r ← elabSimpArgs argsStx initCtx #[] (eraseLocal := false) (kind := .simp)
  let ctx ← addNormalizedUserSimpArgs r.ctx r.simpArgs
  let methods := mkLensSimpMethods r.simprocs
  let runAt (fvarIds : Array FVarId) (simplifyTarget : Bool) : TacticM Unit := do
    let mvarId ← getMainGoal
    match ← lensSimpGoal mvarId ctx methods simplifyTarget fvarIds with
    | none => replaceMainGoal []
    | some (_, mvarIdNew) => replaceMainGoal [mvarIdNew]
  match loc with
  | .targets hyps simplifyTarget =>
    let fvarIds ← getFVarIds hyps
    runAt fvarIds simplifyTarget
  | .wildcard =>
    runAt (← (← getMainGoal).getNondepPropHyps) true

/-- Targeted definitional-reduction pass for concrete optic expressions: unfolds only optic
combinators and `make_lenses` field lenses for structures mentioned in the target/location,
leaving opaque user functions untouched and incurring zero `Eq.trans` proof-term overhead. -/
syntax (name := lensDSimpTac)
  "lens_dsimp" (Lean.Parser.Tactic.location)? : tactic

@[tactic lensDSimpTac]
def evalLensDSimp : Tactic := fun stx => withMainContext do
  let loc := expandOptLocation stx[1]
  let runAt (fvarIds : Array FVarId) (simplifyTarget : Bool) : TacticM Unit := do
    let mvarId ← getMainGoal
    match ← lensDSimpGoal mvarId simplifyTarget fvarIds with
    | none => replaceMainGoal []
    | some mvarIdNew => replaceMainGoal [mvarIdNew]
  match loc with
  | .targets hyps simplifyTarget =>
    let fvarIds ← getFVarIds hyps
    runAt fvarIds simplifyTarget
  | .wildcard =>
    runAt (← (← getMainGoal).getNondepPropHyps) true

end Optic.Tactic

end
