module

public import Lens.Basic

/-!
# Lens-Based Frame Relations (`EqOn`, `Modifies`, `ModifiesAny`, `LensFamily`)

Decoupled, architecture-independent frame specifications built purely on `Optic.Lens` and
`Optic.Getter`:

- `EqOn g s' s` / `EqOnAll gs s' s`: `s'` and `s` agree on the given getter(s) (generalizes
  `Kraken.RegFile.EqOn` and `Kraken.RegFile.View` to arbitrary types and nested projections).
- `Modifies l s' s`: `s'` differs from `s` *at most* on the focus of lens `l`
  (`∃ v, s' = l.set s v`), without requiring a finite enumeration of all fields.
- `ModifiesAny ls s' s`: reflexive-transitive closure of `Modifies` across a list of lenses
  (generalizes `Kraken.RegFile.EqExcept` to heterogeneous, nested, or even overlapping lenses).
- `LensFamily` / `LawfulLensFamily`: an indexed family of pairwise-disjoint complete lenses,
  together with `LawfulLensFamily.modifiesAny_iff` bridging `ModifiesAny` to pointwise
  agreement outside a write set.
-/

@[expose] public section

namespace Optic

universe u v w

/-! ### Heterogeneous Optic Wrappers -/

/-- Existential wrapper around a `Getter s α`, allowing heterogeneous lists of views/fields. -/
structure AnyGetter (s : Type u) where of ::
  {α : Type v}
  getter : Getter s α

namespace AnyGetter

abbrev ofFn {s : Type u} {α : Type v} (f : s → α) : AnyGetter s := ⟨Getter.of f⟩
abbrev ofLens {s : Type u} {α : Type v} (l : Lens s α) : AnyGetter s := ⟨l.toGetter⟩
abbrev ofIso {s : Type u} {α : Type v} (i : Iso s α) : AnyGetter s := ⟨i.toGetter⟩

/-- Lift a getter on an inner state `a` to an outer state `s` through `outer : Getter s a`. -/
abbrev comp {s : Type u} {a : Type v} (outer : Getter s a) (g : AnyGetter.{v, w} a) :
    AnyGetter.{u, w} s :=
  ⟨outer.comp g.getter⟩

end AnyGetter

/-- Existential wrapper around a `Lens s α`, allowing heterogeneous write-sets of lenses. -/
structure AnyLens (s : Type u) where of ::
  {α : Type v}
  lens : Lens s α

namespace AnyLens

abbrev ofIso {s : Type u} {α : Type v} (i : Iso s α) : AnyLens s := ⟨i.toLens⟩

/-- Lift a lens on an inner state `a` to an outer state `s` through `outer : Lens s a`. -/
abbrev comp {s : Type u} {a : Type v} (outer : Lens s a) (l : AnyLens.{v, w} a) :
    AnyLens.{u, w} s :=
  ⟨outer.comp l.lens⟩

end AnyLens

/-- Typeclass coercion into `AnyGetter s` for ergonomic `on [...]` frame lists. -/
class ToAnyGetter (s : Type u) (T : Type w) where
  toAnyGetter : T → AnyGetter.{u, v} s

instance {s : Type u} {α : Type v} : ToAnyGetter.{u, v} s (Getter s α) where
  toAnyGetter := AnyGetter.of

instance {s : Type u} {α : Type v} : ToAnyGetter.{u, v} s (Lens s α) where
  toAnyGetter := AnyGetter.ofLens

instance {s : Type u} {α : Type v} : ToAnyGetter.{u, v} s (Iso s α) where
  toAnyGetter := AnyGetter.ofIso

instance {s : Type u} {α : Type v} : ToAnyGetter.{u, v} s (s → α) where
  toAnyGetter := AnyGetter.ofFn

instance {s : Type u} : ToAnyGetter.{u, v} s (AnyGetter.{u, v} s) where
  toAnyGetter := id

/-- Typeclass coercion into `AnyLens s` for ergonomic `except [...]` frame lists. -/
class ToAnyLens (s : Type u) (T : Type w) where
  toAnyLens : T → AnyLens.{u, v} s

instance {s : Type u} {α : Type v} : ToAnyLens.{u, v} s (Lens s α) where
  toAnyLens := AnyLens.of

instance {s : Type u} {α : Type v} : ToAnyLens.{u, v} s (Iso s α) where
  toAnyLens := AnyLens.ofIso

instance {s : Type u} : ToAnyLens.{u, v} s (AnyLens.{u, v} s) where
  toAnyLens := id

/-! ### Preservation Relations (`EqOn`, `EqOnAll`) -/

/-- `s'` and `s` agree on the projection `g`. -/
def EqOn {s : Type u} {a : Type v} (g : Getter s a) (s' s : s) : Prop :=
  g.get s' = g.get s

namespace EqOn

@[refl] theorem refl {s : Type u} {a : Type v} (g : Getter s a) (x : s) : EqOn g x x :=
  rfl

@[symm] theorem symm {s : Type u} {a : Type v} {g : Getter s a} {s' s : s}
    (h : EqOn g s' s) : EqOn g s s' :=
  Eq.symm h

theorem comp {s : Type u} {a : Type v} {g : Getter s a} {s₁ s₂ s₃ : s}
    (h₁ : EqOn g s₂ s₁) (h₂ : EqOn g s₃ s₂) : EqOn g s₃ s₁ :=
  Eq.trans h₂ h₁

instance {s : Type u} {a : Type v} {g : Getter s a} : Trans (EqOn g) (EqOn g) (EqOn g) where trans a b := comp b a

end EqOn

/-- `s'` and `s` agree on every getter in `gs`. -/
def EqOnAll {s : Type u} (gs : List (AnyGetter.{u, v} s)) (s' s : s) : Prop :=
  ∀ g ∈ gs, g.getter.get s' = g.getter.get s

namespace EqOnAll

@[refl] theorem refl {s : Type u} (gs : List (AnyGetter.{u, v} s)) (x : s) : EqOnAll gs x x :=
  fun _ _ => rfl

@[symm] theorem symm {s : Type u} {gs : List (AnyGetter.{u, v} s)} {s' s : s}
    (h : EqOnAll gs s' s) : EqOnAll gs s s' :=
  fun g hg => (h g hg).symm

theorem comp {s : Type u} {gs : List (AnyGetter.{u, v} s)} {s₁ s₂ s₃ : s}
    (h₁ : EqOnAll gs s₂ s₁) (h₂ : EqOnAll gs s₃ s₂) : EqOnAll gs s₃ s₁ :=
  fun g hg => (h₂ g hg).trans (h₁ g hg)

instance {s : Type u} {gs : List (AnyGetter.{u, v} s)} :
    Trans (EqOnAll gs) (EqOnAll gs) (EqOnAll gs) where trans a b := comp b a

theorem nil {S : Type u} (s' s : S) : EqOnAll ([] : List (AnyGetter.{u, v} S)) s' s :=
  fun _ h => nomatch h

theorem cons {S : Type u} {g : AnyGetter.{u, v} S} {gs : List (AnyGetter.{u, v} S)} {s' s : S}
    (h : g.getter.get s' = g.getter.get s) (hs : EqOnAll gs s' s) :
    EqOnAll (g :: gs) s' s := by
  intro g' hg'
  cases hg' with
  | head => exact h
  | tail _ hg'' => exact hs g' hg''

theorem of_mem {S : Type u} {gs : List (AnyGetter.{u, v} S)} {s' s : S}
    (h : EqOnAll gs s' s) {g : AnyGetter.{u, v} S} (hg : g ∈ gs) :
    g.getter.get s' = g.getter.get s :=
  h g hg

theorem mono {s : Type u} {gs₁ gs₂ : List (AnyGetter.{u, v} s)} {s' s : s}
    (h : EqOnAll gs₂ s' s) (hsub : ∀ g ∈ gs₁, g ∈ gs₂) :
    EqOnAll gs₁ s' s :=
  fun g hg => h g (hsub g hg)

theorem append {s : Type u} {gs₁ gs₂ : List (AnyGetter.{u, v} s)} {s' s : s}
    (h₁ : EqOnAll gs₁ s' s) (h₂ : EqOnAll gs₂ s' s) :
    EqOnAll (gs₁ ++ gs₂) s' s := by
  intro g hg
  rcases List.mem_append.mp hg with hg₁ | hg₂
  · exact h₁ g hg₁
  · exact h₂ g hg₂

theorem lift {s : Type u} {a : Type v} (outer : Getter s a)
    {gs : List (AnyGetter.{v, w} a)} {s' s : s}
    (h : EqOnAll gs (outer.get s') (outer.get s)) :
    EqOnAll (gs.map (AnyGetter.comp outer)) s' s := by
  intro g hg
  rcases List.mem_map.mp hg with ⟨g₀, hg₀, rfl⟩
  exact h g₀ hg₀

end EqOnAll

/-! ### Single-Lens Modification Frame (`Modifies`) -/

/-- `s'` differs from `s` at most on the focus of lens `l`: `s'` can be obtained from `s`
by setting `l` to some value. -/
def Modifies {s : Type u} {a : Type v} (l : Lens s a) (s' s : s) : Prop :=
  ∃ v : a, s' = l.set s v

namespace Modifies

/-- Characterization by updating `s` with `l.get s'`. -/
-- NOTE: I don't like the `set_get` name. Maybe `iff_update` makes more sense, to play off `iff_restore`.
theorem iff_set_get {s : Type u} {a : Type v} {l : Lens s a} [LawfulLens l] {s' s : s} :
    Modifies l s' s ↔ s' = l.set s (l.get s') := by
  constructor
  · rintro ⟨v, rfl⟩
    simp
  · intro h
    exact ⟨l.get s', h⟩

/-- Characterization by restoring `l.get s` into `s'`. -/
theorem iff_restore {s : Type u} {a : Type v} {l : Lens s a} [LawfulLens l] {s' s : s} :
    Modifies l s' s ↔ l.set s' (l.get s) = s := by
  constructor
  · rintro ⟨v, rfl⟩
    simp
  · intro h
    refine ⟨l.get s', ?_⟩
    rw [← h]
    simp

@[refl] theorem refl {s : Type u} {a : Type v} (l : Lens s a) [LawfulLens l] (x : s) :
    Modifies l x x :=
  ⟨l.get x, (Lens.set_get l x).symm⟩

@[symm] theorem symm {s : Type u} {a : Type v} {l : Lens s a} [LawfulLens l] {s' s : s}
    (h : Modifies l s' s) : Modifies l s s' :=
  iff_restore.mpr (iff_set_get.mp h).symm

theorem comp {s : Type u} {a : Type v} {l : Lens s a} [LawfulLens l] {s₁ s₂ s₃ : s}
    (h₁ : Modifies l s₂ s₁) (h₂ : Modifies l s₃ s₂) : Modifies l s₃ s₁ := by
  rcases h₁ with ⟨v₁, rfl⟩
  rcases h₂ with ⟨v₂, rfl⟩
  exact ⟨v₂, by simp⟩

instance {s : Type u} {a : Type v} {l : Lens s a} [LawfulLens l] :
    Trans (Modifies l) (Modifies l) (Modifies l) where trans a b := comp b a

theorem set {s : Type u} {a : Type v} (l : Lens s a) (x : s) (v : a) :
    Modifies l (l.set x v) x :=
  ⟨v, rfl⟩

theorem over {s : Type u} {a : Type v} (l : Lens s a) (f : a → a) (x : s) :
    Modifies l (l.over f x) x :=
  ⟨f (l.get x), rfl⟩

/-- Any `Getter` independent of `l` is preserved across `Modifies l`. -/
theorem preserves {s : Type u} {a : Type v} {b : Type w}
    {l : Lens s a} {g : Getter s b} {s' s : s}
    (hind : Independent l g) (h : Modifies l s' s) :
    g.get s' = g.get s := by
  rcases h with ⟨v, rfl⟩
  exact hind s v

/-- Any lawful `Lens` disjoint from `l` is preserved across `Modifies l`. -/
theorem preserves_disjoint {s : Type u} {a : Type v} {b : Type w}
    {l : Lens s a} {k : Lens s b} [LawfulLens k] {s' s : s}
    (hdisj : Disjoint l k) (h : Modifies l s' s) :
    k.get s' = k.get s :=
  preserves hdisj.independent_left h

/-- Modifying a subfield through `outer ∘ₗ inner` implies modifying `outer`. -/
theorem coarsen {s : Type u} {a : Type v} {b : Type w}
    {outer : Lens s a} {inner : Lens a b} {s' s : s}
    (h : Modifies (outer.comp inner) s' s) :
    Modifies outer s' s := by
  rcases h with ⟨v, rfl⟩
  exact ⟨inner.set (outer.get s) v, rfl⟩

/-- Modifying through `l.comp i.toLens` is equivalent to modifying `l` when `i` is lawful. -/
theorem compIso_iff {s : Type u} {a : Type v} {b : Type w}
    {l : Lens s a} {i : Iso a b} [LawfulIso i] {s' s : s} :
    Modifies (l.comp i.toLens) s' s ↔ Modifies l s' s := by
  constructor
  · exact coarsen
  · rintro ⟨v, rfl⟩
    exact ⟨i.to v, by simp [LawfulIso.inv_to]⟩

/-- Lift a modification on an inner state `a` to the outer state `s`. -/
theorem lift {s : Type u} {a : Type v} {b : Type w}
    (outer : Lens s a) {inner : Lens a b} {x : s} {a' : a}
    (h : Modifies inner a' (outer.get x)) :
    Modifies (outer.comp inner) (outer.set x a') x := by
  rcases h with ⟨v, rfl⟩
  exact ⟨v, rfl⟩

end Modifies

/-! ### Multi-Lens Modification Frame (`ModifiesAny`) -/

/-- `ModifiesAny ls s' s` holds when `s'` is reachable from `s` by modifying only lenses in `ls`.
Unlike flat field-enumeration frames, this requires neither finiteness of the state nor
disjointness of the lenses in `ls`. -/
inductive ModifiesAny {s : Type u} (ls : List (AnyLens.{u, v} s)) : s → s → Prop where
  | refl (x : s) : ModifiesAny ls x x
  | step {l : AnyLens.{u, v} s} {s₁ s₂ s₃ : s}
      (hmem : l ∈ ls)
      (hmod : Modifies l.lens s₂ s₁)
      (hrest : ModifiesAny ls s₃ s₂) :
      ModifiesAny ls s₃ s₁

namespace ModifiesAny

theorem single {s : Type u} {ls : List (AnyLens.{u, v} s)} {l : AnyLens.{u, v} s} {s' s : s}
    (hmem : l ∈ ls) (hmod : Modifies l.lens s' s) :
    ModifiesAny ls s' s :=
  ModifiesAny.step hmem hmod (ModifiesAny.refl s')

theorem set {s : Type u} {ls : List (AnyLens.{u, v} s)} {a : Type v} (l : Lens s a)
    (hmem : AnyLens.of l ∈ ls) (x : s) (val : a) :
    ModifiesAny ls (l.set x val) x :=
  single hmem (Modifies.set l x val)

theorem over {s : Type u} {ls : List (AnyLens.{u, v} s)} {a : Type v} (l : Lens s a)
    (hmem : AnyLens.of l ∈ ls) (f : a → a) (x : s) :
    ModifiesAny ls (l.over f x) x :=
  single hmem (Modifies.over l f x)

theorem comp {s : Type u} {ls : List (AnyLens.{u, v} s)} {s₁ s₂ s₃ : s}
    (h₁ : ModifiesAny ls s₂ s₁) (h₂ : ModifiesAny ls s₃ s₂) :
    ModifiesAny ls s₃ s₁ := by
  induction h₁ with
  | refl => exact h₂
  | step hmem hmod _ ih => exact ModifiesAny.step hmem hmod (ih h₂)

theorem symm {s : Type u} {ls : List (AnyLens.{u, v} s)} {s' s : s}
    (hlaw : ∀ l ∈ ls, LawfulLens l.lens) (h : ModifiesAny ls s' s) :
    ModifiesAny ls s s' := by
  induction h with
  | refl x => exact ModifiesAny.refl x
  | step hmem hmod _ ih =>
    haveI : LawfulLens _ := hlaw _ hmem
    exact comp ih (single hmem hmod.symm)

theorem mono {s : Type u} {ls₁ ls₂ : List (AnyLens.{u, v} s)} {s' s : s}
    (hsub : ∀ l ∈ ls₁, l ∈ ls₂) (h : ModifiesAny ls₁ s' s) :
    ModifiesAny ls₂ s' s := by
  induction h with
  | refl x => exact ModifiesAny.refl x
  | step hmem hmod _ ih => exact ModifiesAny.step (hsub _ hmem) hmod ih

theorem append {s : Type u} {ls₁ ls₂ : List (AnyLens.{u, v} s)} {s₁ s₂ s₃ : s}
    (h₁ : ModifiesAny ls₁ s₂ s₁) (h₂ : ModifiesAny ls₂ s₃ s₂) :
    ModifiesAny (ls₁ ++ ls₂) s₃ s₁ :=
  comp
    (mono (fun _ hm => List.mem_append_left ls₂ hm) h₁)
    (mono (fun _ hm => List.mem_append_right ls₁ hm) h₂)

theorem nil_iff {S : Type u} {s' s : S} :
    ModifiesAny ([] : List (AnyLens.{u, v} S)) s' s ↔ s' = s := by
  constructor
  · intro h
    cases h with
    | refl => rfl
    | step hmem => cases hmem
  · rintro rfl
    exact ModifiesAny.refl s'

theorem singleton_iff {s : Type u} {a : Type v} {l : Lens s a} [LawfulLens l] {s' s : s} :
    ModifiesAny [AnyLens.of l] s' s ↔ Modifies l s' s := by
  constructor
  · intro h
    induction h with
    | refl x => exact Modifies.refl l x
    | step hmem hmod _ ih =>
      simp only [List.mem_singleton] at hmem
      subst hmem
      simp at hmod
      exact trans ih hmod
  · intro h
    exact single (List.mem_singleton_self _) h

/-- Any getter independent of every lens in `ls` is preserved across `ModifiesAny ls`. -/
theorem preserves {s : Type u} {b : Type w} {ls : List (AnyLens.{u, v} s)} {g : Getter s b}
    {s' s : s} (hind : ∀ l ∈ ls, Independent l.lens g) (h : ModifiesAny ls s' s) :
    g.get s' = g.get s := by
  induction h with
  | refl => rfl
  | step hmem hmod _ ih =>
    exact ih.trans (Modifies.preserves (hind _ hmem) hmod)

/-- Narrow a `ModifiesAny` (`except`) frame into an `EqOnAll` (`on`) frame over arbitrary
getters and derived views. -/
theorem preserves_all {s : Type u} {ls : List (AnyLens.{u, v} s)} {gs : List (AnyGetter.{u, w} s)}
    {s' s : s} (hind : ∀ l ∈ ls, ∀ g ∈ gs, Independent l.lens g.getter)
    (h : ModifiesAny ls s' s) :
    EqOnAll gs s' s :=
  fun g hg => preserves (fun l hl => hind l hl g hg) h

/-- Lift a multi-lens frame on a substate `a` through a lawful outer lens `outer : Lens s a`. -/
theorem lift {s : Type u} {a : Type v} (outer : Lens s a) [LawfulLens outer]
    {ls : List (AnyLens.{v, w} a)} {a' : a} {x : s}
    (h : ModifiesAny ls a' (outer.get x)) :
    ModifiesAny (ls.map (AnyLens.comp outer)) (outer.set x a') x := by
  suffices ∀ {a₁ a₂ : a}, ModifiesAny ls a₂ a₁ → ∀ y : s, outer.get y = a₁ →
      ModifiesAny (ls.map (AnyLens.comp outer)) (outer.set y a₂) y from
    this h x rfl
  intro a₁ a₂ h'
  induction h' with
  | refl a₁ =>
    intro y hy
    rw [← hy, Lens.set_get]
    exact ModifiesAny.refl y
  | @step l mid₁ mid₂ mid₃ hmem hmod _ ih =>
    intro y hy
    rcases hmod with ⟨val, rfl⟩
    let y₂ := (outer.comp l.lens).set y val
    have hstep : Modifies (outer.comp l.lens) y₂ y := ⟨val, rfl⟩
    have hy₂ : outer.get y₂ = l.lens.set mid₁ val := by
      simp [y₂, hy]
    have hrest := ih y₂ hy₂
    have hset : outer.set y₂ mid₃ = outer.set y mid₃ := by
      simp [y₂]
    rw [hset] at hrest
    exact ModifiesAny.step (List.mem_map.mpr ⟨l, hmem, rfl⟩) hstep hrest

end ModifiesAny

end Optic

end
