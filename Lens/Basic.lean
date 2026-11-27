module

/-!
# Optics: Getters, Isomorphisms, and Lenses

A general-purpose, standalone optics library for Lean 4 inspired by Haskell's `lens` package.
Provides concrete, proof-friendly definitions of `Getter`, `Iso`, and `Lens`, their laws
(`LawfulIso`, `LawfulLens`), Van Laarhoven functorial modification (`modifyF`), and
orthogonality relations (`Independent`, `Disjoint`) with full compositional closure.
-/

@[expose] public section

namespace Optic

universe u v w u₁ u₂

/-! ### Getters -/

/-- A read-only projection from `s` to `a`. -/
structure Getter (s : Type u) (a : Type v) where of ::
  get : s → a

namespace Getter

/-- The identity getter. -/
nonrec abbrev id {s : Type u} : Getter s s := of id

/-- Outer-to-inner composition of getters. -/
abbrev comp {s : Type u} {a : Type v} {b : Type w}
    (g₁ : Getter s a) (g₂ : Getter a b) : Getter s b :=
  ⟨fun x => g₂.get (g₁.get x)⟩

/-- Post-compose a getter with a function. -/
abbrev map {s : Type u} {a : Type v} {b : Type w}
    (f : a → b) (g : Getter s a) : Getter s b :=
  ⟨fun x => f (g.get x)⟩

/-- Combine two getters on the same source into a pair getter. -/
abbrev prod {s : Type u} {a : Type v} {b : Type w}
    (g₁ : Getter s a) (g₂ : Getter s b) : Getter s (a × b) :=
  ⟨fun x => (g₁.get x, g₂.get x)⟩

/-- Constant getter ignoring the source. -/
abbrev const {s : Type u} {a : Type v} (c : a) : Getter s a :=
  ⟨fun _ => c⟩

section laws

@[simp] theorem of_get {s : Type u} {a : Type v} (f : s → a) (x : s) :
    (Getter.of f).get x = f x := rfl

@[simp] theorem id_get {s : Type u} (x : s) : Getter.id.get x = x := rfl

@[simp] theorem comp_get {s : Type u} {a : Type v} {b : Type w}
    (g₁ : Getter s a) (g₂ : Getter a b) (x : s) :
    (g₁.comp g₂).get x = g₂.get (g₁.get x) := rfl

@[simp] theorem map_get {s : Type u} {a : Type v} {b : Type w}
    (f : a → b) (g : Getter s a) (x : s) :
    (g.map f).get x = f (g.get x) := rfl

@[simp] theorem prod_get {s : Type u} {a : Type v} {b : Type w}
    (g₁ : Getter s a) (g₂ : Getter s b) (x : s) :
    (g₁.prod g₂).get x = (g₁.get x, g₂.get x) := rfl

@[simp] theorem const_get {s : Type u} {a : Type v} (c : a) (x : s) :
    (Getter.const c).get x = c := rfl
end laws

end Getter

/-! ### Isomorphisms -/

/-- A reversible transformation between `s` and `a`. -/
structure Iso (s : Type u) (a : Type v) where
  to : s → a
  inv : a → s

/-- Lawfulness for an `Iso`: `to` and `inv` are mutual inverses. -/
class LawfulIso {s : Type u} {a : Type v} (i : Iso s a) : Prop where
  inv_to : ∀ x : s, i.inv (i.to x) = x
  to_inv : ∀ y : a, i.to (i.inv y) = y

namespace Iso

/-- The identity isomorphism. -/
@[refl] abbrev id {s : Type u} : Iso s s := ⟨fun x => x, fun x => x⟩

/-- Invert an isomorphism (Haskell `lens`: `from`). -/
@[symm] abbrev symm {s : Type u} {a : Type v} (i : Iso s a) : Iso a s :=
  ⟨i.inv, i.to⟩

/-- Outer-to-inner composition of isomorphisms. -/
abbrev comp {s : Type u} {a : Type v} {b : Type w}
    (i₁ : Iso s a) (i₂ : Iso a b) : Iso s b :=
  ⟨fun x => i₂.to (i₁.to x), fun y => i₁.inv (i₂.inv y)⟩

instance : Trans Iso Iso Iso where trans := comp

/-- View an isomorphism as a `Getter`. -/
abbrev toGetter {s : Type u} {a : Type v} (i : Iso s a) : Getter s a :=
  ⟨i.to⟩

instance lawful_id {s : Type u} : LawfulIso (Iso.id (s := s)) where
  inv_to _ := rfl
  to_inv _ := rfl

instance lawful_symm {s : Type u} {a : Type v} (i : Iso s a) [LawfulIso i] :
    LawfulIso i.symm where
  inv_to := LawfulIso.to_inv (i := i)
  to_inv := LawfulIso.inv_to (i := i)

instance lawful_comp {s : Type u} {a : Type v} {b : Type w}
    (i₁ : Iso s a) (i₂ : Iso a b) [LawfulIso i₁] [LawfulIso i₂] :
    LawfulIso (i₁.comp i₂) where
  inv_to x := by simp [LawfulIso.inv_to]
  to_inv y := by simp [LawfulIso.to_inv]

-- NOTE: This is not needed here. Move it to the examples files, or to a
-- separate "impl" file, if anything.
/-- Standard isomorphism between `UInt64` and `BitVec 64`. -/
abbrev uint64BitVec : Iso UInt64 (BitVec 64) where
  to := UInt64.toBitVec
  inv := UInt64.ofBitVec

instance lawful_uint64BitVec : LawfulIso Iso.uint64BitVec where
  inv_to x := by cases x; rfl
  to_inv _ := rfl

end Iso

/-! ### Lenses -/

/-- A first-class functional reference focusing on a field or subfield `a` inside `s`. -/
structure Lens (s : Type u) (a : Type v) where
  get : s → a
  set : s → a → s

/-- The three standard lens laws (PutGet, GetPut, PutPut). -/
class LawfulLens {s : Type u} {a : Type v} (l : Lens s a) : Prop where
  get_set : ∀ (x : s) (v : a), l.get (l.set x v) = v
  set_get : ∀ (x : s), l.set x (l.get x) = x
  set_set : ∀ (x : s) (v₁ v₂ : a), l.set (l.set x v₁) v₂ = l.set x v₂

namespace Lens

/-- Read the focused value (alias for `get`, matching Haskell `lens`). -/
abbrev view {s : Type u} {a : Type v} (l : Lens s a) (x : s) : a :=
  l.get x

/-- Apply a pure function to the focused value (Haskell `lens`: `over`). -/
abbrev over {s : Type u} {a : Type v} (l : Lens s a) (f : a → a) (x : s) : s :=
  l.set x (f (l.get x))

/-- Van Laarhoven functorial lens action: apply an effectful function `a → f a` at the focus. -/
def modifyF {s a : Type u} {f : Type u → Type w} [Functor f]
    (l : Lens s a) (fn : a → f a) (x : s) : f s :=
  l.set x <$> fn (l.get x)

/-- Forget the setter and treat a `Lens` as a `Getter`. -/
abbrev toGetter {s : Type u} {a : Type v} (l : Lens s a) : Getter s a :=
  ⟨l.get⟩

instance {s : Type u} {a : Type v} : Coe (Lens s a) (Getter s a) where
  coe := Lens.toGetter

/-- The identity lens focusing on the whole value. -/
@[refl] abbrev id {s : Type u} : Lens s s where
  get x := x
  set _ v := v

/-- The trivial empty lens focusing on `PUnit` (models an empty write set `except []`). -/
abbrev unit {s : Type u} : Lens s PUnit.{v + 1} where
  get _ := PUnit.unit
  set x _ := x

/-- Outer-to-inner composition of lenses: focus on `a` inside `s`, then `b` inside `a`. -/
abbrev comp {s : Type u} {a : Type v} {b : Type w}
    (outer : Lens s a) (inner : Lens a b) : Lens s b where
  get x := inner.get (outer.get x)
  set x v := outer.set x (inner.set (outer.get x) v)

instance : Trans Lens Lens Lens where trans := comp

/-- Combine two lenses on the same source into a product lens (lawful when disjoint). -/
abbrev prod {s : Type u} {a : Type v} {b : Type w}
    (l₁ : Lens s a) (l₂ : Lens s b) : Lens s (a × b) where
  get x := (l₁.get x, l₂.get x)
  set x p := l₂.set (l₁.set x p.1) p.2

/-- Lens focusing on the first component of a pair (Haskell `lens`: `_1`). -/
abbrev fst {a : Type u} {b : Type v} : Lens (a × b) a where
  get p := p.1
  set p x := (x, p.2)

/-- Lens focusing on the second component of a pair (Haskell `lens`: `_2`). -/
abbrev snd {a : Type u} {b : Type v} : Lens (a × b) b where
  get p := p.2
  set p y := (p.1, y)

/-- Lens focusing on a single key of a total function `k → v`. -/
def atKey {k : Type u} {v : Type v} [DecidableEq k] (key : k) : Lens (k → v) v where
  get f := f key
  set f val k' := if k' = key then val else f k'

section laws

/-! #### Basic `simp` and Lawfulness Lemmas -/

@[simp] theorem get_set {s : Type u} {a : Type v} (l : Lens s a) [LawfulLens l] (x : s) (v : a) :
    l.get (l.set x v) = v :=
  LawfulLens.get_set x v

@[simp] theorem set_get {s : Type u} {a : Type v} (l : Lens s a) [LawfulLens l] (x : s) :
    l.set x (l.get x) = x :=
  LawfulLens.set_get x

@[simp] theorem set_set {s : Type u} {a : Type v} (l : Lens s a) [LawfulLens l]
    (x : s) (v₁ v₂ : a) :
    l.set (l.set x v₁) v₂ = l.set x v₂ :=
  LawfulLens.set_set x v₁ v₂

@[simp] theorem over_id {s : Type u} {a : Type v} (l : Lens s a) [LawfulLens l] (x : s) :
    l.over _root_.id x = x :=
  LawfulLens.set_get x

@[simp] theorem over_comp {s : Type u} {a : Type v} (l : Lens s a) [LawfulLens l]
    (f g : a → a) (x : s) :
    l.over g (l.over f x) = l.over (g ∘ f) x := by
  simp [Lens.over]

@[simp] theorem get_over {s : Type u} {a : Type v} (l : Lens s a) [LawfulLens l]
    (f : a → a) (x : s) :
    l.get (l.over f x) = f (l.get x) := by
  simp [Lens.over]

@[simp] theorem set_over {s : Type u} {a : Type v} (l : Lens s a) [LawfulLens l]
    (f : a → a) (x : s) (v : a) :
    l.set (l.over f x) v = l.set x v := by
  simp [Lens.over]

@[simp] theorem over_set {s : Type u} {a : Type v} (l : Lens s a) [LawfulLens l]
    (f : a → a) (x : s) (v : a) :
    l.over f (l.set x v) = l.set x (f v) := by
  simp [Lens.over]

theorem modifyF_id {s a : Type u} (l : Lens s a) [LawfulLens l] (x : s) :
    l.modifyF (f := Id) pure x = pure x := by
  change l.set x (l.get x) = x
  exact LawfulLens.set_get x

instance lawful_id {s : Type u} : LawfulLens (Lens.id (s := s)) where
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

instance lawful_unit {s : Type u} : LawfulLens (Lens.unit.{u, v} (s := s)) where
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

theorem comp_prod_set {s : Type u} {a : Type v} {b : Type w} {c : Type u₁}
    (outer : Lens s a) [LawfulLens outer] (inner₁ : Lens a b) (inner₂ : Lens a c)
    (x : s) (p : b × c) :
    (outer.comp (inner₁.prod inner₂)).set x p =
      ((outer.comp inner₁).prod (outer.comp inner₂)).set x p := by
  simp

instance lawful_comp {s : Type u} {a : Type v} {b : Type w}
    (outer : Lens s a) (inner : Lens a b) [LawfulLens outer] [LawfulLens inner] :
    LawfulLens (outer.comp inner) where
  get_set x v := by simp
  set_get x := by simp
  set_set x v₁ v₂ := by simp

instance lawful_fst {a : Type u} {b : Type v} : LawfulLens (Lens.fst (a := a) (b := b)) where
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

instance lawful_snd {a : Type u} {b : Type v} : LawfulLens (Lens.snd (a := a) (b := b)) where
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

instance lawful_atKey {k : Type u} {v : Type v} [DecidableEq k] (key : k) :
    LawfulLens (Lens.atKey (v := v) key) where
  get_set f val := by simp [Lens.atKey]
  set_get f := by
    funext k'
    simp only [Lens.atKey]
    split
    · next h => subst h; rfl
    · rfl
  set_set f v₁ v₂ := by
    funext k'
    simp only [Lens.atKey]
    split <;> rfl

end laws

end Lens

/-- Every `Iso` induces a `Lens`. -/
def Iso.toLens {s : Type u} {a : Type v} (i : Iso s a) : Lens s a where
  get := i.to
  set _ v := i.inv v

@[simp] theorem Iso.toLens_get {s : Type u} {a : Type v} (i : Iso s a) (x : s) :
    i.toLens.get x = i.to x := rfl

@[simp] theorem Iso.toLens_set {s : Type u} {a : Type v} (i : Iso s a) (x : s) (v : a) :
    i.toLens.set x v = i.inv v := rfl

instance {s : Type u} {a : Type v} : Coe (Iso s a) (Lens s a) where
  coe := Iso.toLens

instance Iso.lawful_toLens {s : Type u} {a : Type v} (i : Iso s a) [LawfulIso i] :
    LawfulLens i.toLens where
  get_set _ v := LawfulIso.to_inv v
  set_get x := LawfulIso.inv_to x
  set_set _ _ _ := rfl

/-! ### Orthogonality: `Independent` and `Disjoint` -/

/-- A `Getter` `g` is independent of a `Lens` `l` if updating through `l` never changes `g`. -/
def Independent {s : Type u} {a : Type v} {b : Type w}
    (l : Lens s a) (g : Getter s b) : Prop :=
  ∀ (x : s) (v : a), g.get (l.set x v) = g.get x

/-- Two lenses on the same source are disjoint (orthogonal) if their updates commute.
For lawful lenses, non-interference of `get` (`get₁_set₂`, `get₂_set₁`) follows automatically. -/
def Disjoint {s : Type u} {a : Type v} {b : Type w}
    (l₁ : Lens s a) (l₂ : Lens s b) : Prop :=
  ∀ (x : s) (v₁ : a) (v₂ : b), l₁.set (l₂.set x v₂) v₁ = l₂.set (l₁.set x v₁) v₂

namespace Independent

theorem const {s : Type u} {a : Type v} {b : Type w} (l : Lens s a) (c : b) :
    Independent l (Getter.const c) :=
  fun _ _ => rfl

theorem unit {s : Type u} {b : Type w} (g : Getter s b) :
    Independent (Lens.unit.{u, v} (s := s)) g :=
  fun _ _ => rfl

theorem map {s : Type u} {a : Type v} {b : Type w} {c : Type u₁}
    {l : Lens s a} {g : Getter s b} (f : b → c) (h : Independent l g) :
    Independent l (g.map f) :=
  fun x v => congrArg f (h x v)

theorem comp_getter {s : Type u} {a : Type v} {b : Type w} {c : Type u₁}
    {l : Lens s a} {g₁ : Getter s b} (g₂ : Getter b c) (h : Independent l g₁) :
    Independent l (g₁.comp g₂) :=
  fun x v => congrArg g₂.get (h x v)

theorem prod {s : Type u} {a : Type v} {b : Type w} {c : Type u₁}
    {l : Lens s a} {g₁ : Getter s b} {g₂ : Getter s c}
    (h₁ : Independent l g₁) (h₂ : Independent l g₂) :
    Independent l (g₁.prod g₂) :=
  fun x v => Prod.ext (h₁ x v) (h₂ x v)

theorem comp_lens {s : Type u} {a : Type v} {b : Type w} {c : Type u₁}
    {outer : Lens s a} (inner : Lens a b) {g : Getter s c}
    (h : Independent outer g) :
    Independent (outer.comp inner) g :=
  fun x v => h x (inner.set (outer.get x) v)

theorem comp_same {s : Type u} {a : Type v} {b : Type w} {c : Type u₁}
    (outer : Lens s a) [LawfulLens outer] {inner : Lens a b} {g : Getter a c}
    (h : Independent inner g) :
    Independent (outer.comp inner) (outer.toGetter.comp g) := by
  intro x v
  simp only [Lens.get_set]
  exact h (outer.get x) v

theorem prod_lens {s : Type u} {a : Type v} {b : Type w} {c : Type u₁}
    {l₁ : Lens s a} {l₂ : Lens s b} {g : Getter s c}
    (h₁ : Independent l₁ g) (h₂ : Independent l₂ g) :
    Independent (l₁.prod l₂) g := by
  intro x p
  rw [h₂, h₁]

end Independent

namespace Disjoint

theorem set_comm {s : Type u} {a : Type v} {b : Type w}
    {l₁ : Lens s a} {l₂ : Lens s b} (h : Disjoint l₁ l₂)
    (x : s) (v₁ : a) (v₂ : b) :
    l₁.set (l₂.set x v₂) v₁ = l₂.set (l₁.set x v₁) v₂ :=
  h x v₁ v₂

theorem symm {s : Type u} {a : Type v} {b : Type w}
    {l₁ : Lens s a} {l₂ : Lens s b} (h : Disjoint l₁ l₂) :
    Disjoint l₂ l₁ :=
  fun x v₂ v₁ => (h x v₁ v₂).symm

theorem get₁_set₂ {s : Type u} {a : Type v} {b : Type w}
    {l₁ : Lens s a} {l₂ : Lens s b} [LawfulLens l₁] (h : Disjoint l₁ l₂)
    (x : s) (v : b) :
    l₁.get (l₂.set x v) = l₁.get x := by
  calc l₁.get (l₂.set x v)
      = l₁.get (l₂.set (l₁.set x (l₁.get x)) v) := by rw [Lens.set_get]
    _ = l₁.get (l₁.set (l₂.set x v) (l₁.get x)) := by rw [← h x (l₁.get x) v]
    _ = l₁.get x := Lens.get_set l₁ _ _

theorem get₂_set₁ {s : Type u} {a : Type v} {b : Type w}
    {l₁ : Lens s a} {l₂ : Lens s b} [LawfulLens l₂] (h : Disjoint l₁ l₂)
    (x : s) (v : a) :
    l₂.get (l₁.set x v) = l₂.get x :=
  h.symm.get₁_set₂ x v

theorem independent_left {s : Type u} {a : Type v} {b : Type w}
    {l₁ : Lens s a} {l₂ : Lens s b} [LawfulLens l₂] (h : Disjoint l₁ l₂) :
    Independent l₁ l₂.toGetter :=
  h.get₂_set₁

theorem independent_right {s : Type u} {a : Type v} {b : Type w}
    {l₁ : Lens s a} {l₂ : Lens s b} [LawfulLens l₁] (h : Disjoint l₁ l₂) :
    Independent l₂ l₁.toGetter :=
  h.get₁_set₂

theorem comp_left {s : Type u} {a : Type v} {b : Type w} {c : Type u₁}
    {l₁ : Lens s a} {l₂ : Lens s b} [LawfulLens l₁] (k₁ : Lens a c) (h : Disjoint l₁ l₂) :
    Disjoint (l₁.comp k₁) l₂ := by
  intro x v₁ v₂
  simp only [h.get₁_set₂]
  exact h x (k₁.set (l₁.get x) v₁) v₂

theorem comp_right {s : Type u} {a : Type v} {b : Type w} {c : Type u₁}
    {l₁ : Lens s a} {l₂ : Lens s b} [LawfulLens l₂] (k₂ : Lens b c) (h : Disjoint l₁ l₂) :
    Disjoint l₁ (l₂.comp k₂) :=
  (h.symm.comp_left k₂).symm

theorem comp {s : Type u} {a : Type v} {b : Type w} {c : Type u₁} {d : Type u₂}
    {l₁ : Lens s a} {l₂ : Lens s b} [LawfulLens l₁] [LawfulLens l₂]
    (k₁ : Lens a c) (k₂ : Lens b d) (h : Disjoint l₁ l₂) :
    Disjoint (l₁.comp k₁) (l₂.comp k₂) :=
  (h.comp_left k₁).comp_right k₂

theorem comp_same {s : Type u} {a : Type v} {b : Type w} {c : Type u₁}
    (outer : Lens s a) [LawfulLens outer] {inner₁ : Lens a b} {inner₂ : Lens a c}
    (h : Disjoint inner₁ inner₂) :
    Disjoint (outer.comp inner₁) (outer.comp inner₂) := by
  intro x v₁ v₂
  simp [h.set_comm]

theorem fst_snd {a : Type u} {b : Type v} :
    Disjoint (Lens.fst (a := a) (b := b)) (Lens.snd (a := a) (b := b)) :=
  fun _ _ _ => rfl

theorem unit_left {s : Type u} {b : Type w} (l : Lens s b) :
    Disjoint (Lens.unit.{u, v} (s := s)) l :=
  fun _ _ _ => rfl

theorem unit_right {s : Type u} {a : Type v} (l : Lens s a) :
    Disjoint l (Lens.unit.{u, w} (s := s)) :=
  fun _ _ _ => rfl

theorem prod_left {s : Type u} {a : Type v} {b : Type w} {c : Type u₁}
    {l₁ : Lens s a} {l₂ : Lens s b} {k : Lens s c}
    (h₁ : Disjoint l₁ k) (h₂ : Disjoint l₂ k) :
    Disjoint (l₁.prod l₂) k := by
  intro x p v
  change l₂.set (l₁.set (k.set x v) p.1) p.2 = k.set (l₂.set (l₁.set x p.1) p.2) v
  rw [h₁.set_comm, h₂.set_comm]

theorem prod_right {s : Type u} {a : Type v} {b : Type w} {c : Type u₁}
    {l : Lens s a} {k₁ : Lens s b} {k₂ : Lens s c}
    (h₁ : Disjoint l k₁) (h₂ : Disjoint l k₂) :
    Disjoint l (k₁.prod k₂) :=
  (prod_left h₁.symm h₂.symm).symm

theorem atKey_of_ne {k : Type u} {v : Type v} [DecidableEq k] {k₁ k₂ : k} (hne : k₁ ≠ k₂) :
    Disjoint (Lens.atKey (v := v) k₁) (Lens.atKey (v := v) k₂) := by
  intro f v₁ v₂
  funext k'
  simp only [Lens.atKey]
  by_cases h1 : k' = k₁
  · subst h1; simp [hne]
  · simp [h1]

end Disjoint

/-- The product of two disjoint lawful lenses is itself a lawful lens. -/
theorem Lens.lawful_prod {s : Type u} {a : Type v} {b : Type w}
    (l₁ : Lens s a) (l₂ : Lens s b) [LawfulLens l₁] [LawfulLens l₂] (h : Disjoint l₁ l₂) :
    LawfulLens (l₁.prod l₂) where
  get_set x p :=
    Prod.ext (by dsimp only; rw [h.get₁_set₂, Lens.get_set]) (Lens.get_set l₂ _ _)
  set_get x := by simp only [Lens.set_get]
  set_set x p₁ p₂ := by
    change l₂.set (l₁.set (l₂.set (l₁.set x p₁.1) p₁.2) p₂.1) p₂.2 =
      l₂.set (l₁.set x p₂.1) p₂.2
    rw [← h.set_comm, Lens.set_set, h.set_comm, Lens.set_set]

/-! ### Scoped Haskell-Inspired Notation -/

/-- Polymorphic view projection so `s ^. o` works uniformly for `Lens`, `Getter`, and `Iso`. -/
class HasGet (O : Type u) (s : outParam (Type v)) (a : outParam (Type w)) where
  getOf : O → s → a

instance {s : Type u} {a : Type v} : HasGet (Getter s a) s a where
  getOf := Getter.get

instance {s : Type u} {a : Type v} : HasGet (Lens s a) s a where
  getOf := Lens.get

instance {s : Type u} {a : Type v} : HasGet (Iso s a) s a where
  getOf := Iso.to

end Optic

end
