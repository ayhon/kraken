module

public import Lens.Basic
public import Lens.Frame
public import Lens.Relation

/-!
# Product-Lens Frames (`Modifies`, `FactorsLawful`, and `ReflTransGen`)

Represents multi-field write-set frames using right-associated product lenses (`l₁ ×ₗ l₂ ×ₗ …`)
with `Lens.unit` for the empty write set `except []`, together with their reflexive-transitive
closure `ReflTransGen (Modifies l)`.

## Key Properties
- **1-line concrete proofs:** `Modifies (l₁ ×ₗ l₂)` is `∃ p, s' = (l₁ ×ₗ l₂).set s p`, so
  concrete multi-field updates are proved by `ReflTransGen.single ⟨(v₁, (v₂, v₃)), rfl⟩`
  without intermediate state chains or `List.mem` proofs.
- **Unconditional algebra under `ReflTransGen` + `FactorsLawful`:** Because `set_get` (and
  hence `Modifies.refl`) lifts through `×ₗ` *without* `Disjoint`, `FactorsLawful` synthesizes
  automatically for arbitrary products and compositions of lawful lenses. Wrapping `Modifies`
  in `ReflTransGen` then gives unconditional reflexivity, transitivity, symmetry, reordering,
  deduplication, coarsening, and soundness under symbolic aliasing (e.g., `atKey i ×ₗ atKey j`
  without knowing `i ≠ j`) — with zero `Disjoint` obligations.
- **Collapses to single-pass `Modifies`:** Whenever `l` is itself a `LawfulLens` (e.g., pairwise
  disjoint product lenses), `ReflTransGen (Modifies l) s' s ↔ Modifies l s' s`.
-/

@[expose] public section

namespace Optic

universe u v w u₁

/-! ### `FactorsLawful`: Compositional Lawfulness Without Disjointness -/

/-- A lens `l` is `FactorsLawful` when every atomic factor in its `×ₗ` / `∘ₗ` tree is lawful:
- `l` satisfies `set_get` (so `Modifies.refl l` holds unconditionally, even for non-disjoint
  products like `atKey i ×ₗ atKey j`); and
- every single `Modifies l` step is reversible in `ReflTransGen (Modifies l)`.

Unlike `LawfulLens (l₁ ×ₗ l₂)`, `FactorsLawful (l₁ ×ₗ l₂)` requires **no** `Disjoint l₁ l₂`
proof, so typeclass resolution synthesizes it automatically for arbitrary lens products. -/
class FactorsLawful {s : Type u} {a : Type v} (l : Lens s a) : Prop where
  set_get : ∀ x : s, l.set x (l.get x) = x
  rev : ∀ x y : s, Modifies l x y → ReflTransGen (Modifies l) y x

namespace Modifies

/-! #### Empty (`Lens.unit`) Frame -/

theorem unit_iff {s : Type u} {s' s₀ : s} :
    Modifies (Lens.unit.{u, v} (s := s)) s' s₀ ↔ s' = s₀ := by
  constructor
  · rintro ⟨_, rfl⟩; rfl
  · rintro rfl; exact ⟨PUnit.unit, rfl⟩

theorem prod_unit_left_iff {s : Type u} {a : Type v} {l : Lens s a} {s' s₀ : s} :
    Modifies ((Lens.unit.{u, w} (s := s)).prod l) s' s₀ ↔ Modifies l s' s₀ := by
  constructor
  · rintro ⟨⟨_, v⟩, rfl⟩; exact ⟨v, rfl⟩
  · rintro ⟨v, rfl⟩; exact ⟨(PUnit.unit, v), rfl⟩

theorem prod_unit_right_iff {s : Type u} {a : Type v} {l : Lens s a} {s' s₀ : s} :
    Modifies (l.prod (Lens.unit.{u, w} (s := s))) s' s₀ ↔ Modifies l s' s₀ := by
  constructor
  · rintro ⟨⟨v, _⟩, rfl⟩; exact ⟨v, rfl⟩
  · rintro ⟨v, rfl⟩; exact ⟨(v, PUnit.unit), rfl⟩

/-! #### Single-Pass Product-Lens Frame Algebra -/

theorem prod_iff_exists {s : Type u} {a : Type v} {b : Type w}
    {l₁ : Lens s a} {l₂ : Lens s b} {s' s₀ : s} :
    Modifies (l₁.prod l₂) s' s₀ ↔ ∃ mid : s, Modifies l₁ mid s₀ ∧ Modifies l₂ s' mid := by
  constructor
  · rintro ⟨⟨v₁, v₂⟩, rfl⟩
    exact ⟨l₁.set s₀ v₁, ⟨v₁, rfl⟩, ⟨v₂, rfl⟩⟩
  · rintro ⟨mid, ⟨v₁, rfl⟩, ⟨v₂, rfl⟩⟩
    exact ⟨(v₁, v₂), rfl⟩

theorem prod_comp {s : Type u} {a : Type v} {b : Type w}
    {l₁ : Lens s a} {l₂ : Lens s b} {s₁ s₂ s₃ : s}
    (h₁ : Modifies l₁ s₂ s₁) (h₂ : Modifies l₂ s₃ s₂) :
    Modifies (l₁.prod l₂) s₃ s₁ :=
  prod_iff_exists.mpr ⟨s₂, h₁, h₂⟩

theorem prod_assoc {s : Type u} {a : Type v} {b : Type w} {c : Type u₁}
    {l₁ : Lens s a} {l₂ : Lens s b} {l₃ : Lens s c} {s' s₀ : s} :
    Modifies ((l₁.prod l₂).prod l₃) s' s₀ ↔ Modifies (l₁.prod (l₂.prod l₃)) s' s₀ := by
  constructor
  · rintro ⟨⟨⟨v₁, v₂⟩, v₃⟩, rfl⟩; exact ⟨(v₁, (v₂, v₃)), rfl⟩
  · rintro ⟨⟨v₁, ⟨v₂, v₃⟩⟩, rfl⟩; exact ⟨((v₁, v₂), v₃), rfl⟩

theorem prod_congr_left {s : Type u} {a : Type v} {a' : Type u₁} {b : Type w}
    {l₁ : Lens s a} {l₁' : Lens s a'} {l₂ : Lens s b} {s' s₀ : s}
    (heq : ∀ x y : s, Modifies l₁ x y ↔ Modifies l₁' x y) :
    Modifies (l₁.prod l₂) s' s₀ ↔ Modifies (l₁'.prod l₂) s' s₀ := by
  simp only [prod_iff_exists, heq]

theorem prod_congr_right {s : Type u} {a : Type v} {b : Type w} {b' : Type u₁}
    {l₁ : Lens s a} {l₂ : Lens s b} {l₂' : Lens s b'} {s' s₀ : s}
    (heq : ∀ x y : s, Modifies l₂ x y ↔ Modifies l₂' x y) :
    Modifies (l₁.prod l₂) s' s₀ ↔ Modifies (l₁.prod l₂') s' s₀ := by
  simp only [prod_iff_exists, heq]

theorem refl_of_set_get {s : Type u} {a : Type v} (l : Lens s a)
    (hsg : ∀ x : s, l.set x (l.get x) = x) (x : s) :
    Modifies l x x :=
  ⟨l.get x, (hsg x).symm⟩

theorem refl_of_factorsLawful {s : Type u} {a : Type v} (l : Lens s a) [h : FactorsLawful l]
    (x : s) : Modifies l x x :=
  refl_of_set_get l h.set_get x

theorem prod_left_of_set_get {s : Type u} {a : Type v} {b : Type w}
    {l₁ : Lens s a} (l₂ : Lens s b) (hsg : ∀ x : s, l₂.set x (l₂.get x) = x)
    {s' s₀ : s} (h : Modifies l₁ s' s₀) :
    Modifies (l₁.prod l₂) s' s₀ :=
  prod_comp h (refl_of_set_get l₂ hsg s')

theorem prod_right_of_set_get {s : Type u} {a : Type v} {b : Type w}
    (l₁ : Lens s a) (hsg : ∀ x : s, l₁.set x (l₁.get x) = x)
    {l₂ : Lens s b} {s' s₀ : s} (h : Modifies l₂ s' s₀) :
    Modifies (l₁.prod l₂) s' s₀ :=
  prod_comp (refl_of_set_get l₁ hsg s₀) h

theorem symm_prod_swap {s : Type u} {a : Type v} {b : Type w}
    {l₁ : Lens s a} {l₂ : Lens s b} [LawfulLens l₁] [LawfulLens l₂] {s' s₀ : s}
    (h : Modifies (l₁.prod l₂) s' s₀) :
    Modifies (l₂.prod l₁) s₀ s' := by
  rcases prod_iff_exists.mp h with ⟨mid, h₁, h₂⟩
  exact prod_comp h₂.symm h₁.symm

theorem prod_comm_iff {s : Type u} {a : Type v} {b : Type w}
    {l₁ : Lens s a} {l₂ : Lens s b} (hdisj : Disjoint l₁ l₂) {s' s₀ : s} :
    Modifies (l₁.prod l₂) s' s₀ ↔ Modifies (l₂.prod l₁) s' s₀ := by
  constructor
  · rintro ⟨⟨v₁, v₂⟩, rfl⟩
    exact ⟨(v₂, v₁), (hdisj.set_comm s₀ v₁ v₂).symm⟩
  · rintro ⟨⟨v₂, v₁⟩, rfl⟩
    exact ⟨(v₁, v₂), hdisj.set_comm s₀ v₁ v₂⟩

theorem symm_prod {s : Type u} {a : Type v} {b : Type w}
    {l₁ : Lens s a} {l₂ : Lens s b} [LawfulLens l₁] [LawfulLens l₂]
    (hdisj : Disjoint l₁ l₂) {s' s₀ : s} (h : Modifies (l₁.prod l₂) s' s₀) :
    Modifies (l₁.prod l₂) s₀ s' := by
  haveI := Lens.lawful_prod l₁ l₂ hdisj
  exact h.symm

theorem comp_prod {s : Type u} {a : Type v} {b : Type w}
    {l₁ : Lens s a} {l₂ : Lens s b} [LawfulLens l₁] [LawfulLens l₂]
    (hdisj : Disjoint l₁ l₂) {s₁ s₂ s₃ : s}
    (h₁ : Modifies (l₁.prod l₂) s₂ s₁) (h₂ : Modifies (l₁.prod l₂) s₃ s₂) :
    Modifies (l₁.prod l₂) s₃ s₁ := by
  haveI := Lens.lawful_prod l₁ l₂ hdisj
  exact h₁.comp h₂

--
-- Eventually (step1 ⸨prog| jz foo⸩) (fun st' => st' = st) ⟨st, addrOf 0⟩

/-! #### Narrowing and Lifting (Single-Pass) -/

theorem preserves_all {s : Type u} {a : Type v} {l : Lens s a}
    {gs : List (AnyGetter.{u, w} s)} {s' s : s}
    (hind : ∀ g ∈ gs, Independent l g.getter)
    (h : Modifies l s' s) :
    EqOnAll gs s' s :=
  fun g hg => preserves (hind g hg) h

theorem comp_prod_iff {s : Type u} {a : Type v} {b : Type w} {c : Type u₁}
    (outer : Lens s a) [LawfulLens outer] {inner₁ : Lens a b} {inner₂ : Lens a c} {s' s₀ : s} :
    Modifies (outer.comp (inner₁.prod inner₂)) s' s₀ ↔
      Modifies ((outer.comp inner₁).prod (outer.comp inner₂)) s' s₀ := by
  constructor <;> rintro ⟨p, rfl⟩
  · exact ⟨p, Lens.comp_prod_set outer inner₁ inner₂ s₀ p⟩
  · exact ⟨p, (Lens.comp_prod_set outer inner₁ inner₂ s₀ p).symm⟩

theorem lift_prod {s : Type u} {a : Type v} {b : Type w} {c : Type u₁}
    (outer : Lens s a) [LawfulLens outer] {inner₁ : Lens a b} {inner₂ : Lens a c}
    {x : s} {a' : a} (h : Modifies (inner₁.prod inner₂) a' (outer.get x)) :
    Modifies ((outer.comp inner₁).prod (outer.comp inner₂)) (outer.set x a') x :=
  (comp_prod_iff outer).mp (lift outer h)

theorem lift_unit {s : Type u} {a : Type v}
    (outer : Lens s a) [LawfulLens outer] {x : s} {a' : a}
    (h : Modifies (Lens.unit.{v, w} (s := a)) a' (outer.get x)) :
    Modifies (Lens.unit.{u, w} (s := s)) (outer.set x a') x := by
  rw [unit_iff] at h ⊢
  rw [h, Lens.set_get]

end Modifies

/-! ### `FactorsLawful` Instances -/

/-- Lift a `ReflTransGen (Modifies inner)` frame on substate `a` through a lawful `outer` lens. -/
theorem Modifies.rt_lift {s : Type u} {a : Type v} {b : Type w}
    (outer : Lens s a) [LawfulLens outer] {inner : Lens a b} {a' : a} {x : s}
    (h : ReflTransGen (Modifies inner) a' (outer.get x)) :
    ReflTransGen (Modifies (outer.comp inner)) (outer.set x a') x := by
  suffices ∀ {a₁ a₂ : a}, ReflTransGen (Modifies inner) a₁ a₂ →
      ∀ y : s, outer.get y = a₂ →
      ReflTransGen (Modifies (outer.comp inner)) (outer.set y a₁) y from
    this h x rfl
  intro a₁ a₂ h'
  induction h' with
  | refl =>
    intro y hy
    rw [← hy, Lens.set_get]
    exact .refl
  | @tail _ mid₂ _ hstep ih =>
    intro y hy
    rcases hstep with ⟨v, rfl⟩
    subst hy
    let y₁ := outer.set y (inner.set (outer.get y) v)
    have h1 : ReflTransGen (Modifies (outer.comp inner)) (outer.set y₁ a₁) y₁ :=
      ih y₁ (by simp [y₁])
    have h2 : Modifies (outer.comp inner) y₁ y :=
      Modifies.lift outer (Modifies.set inner (outer.get y) v)
    have hset : outer.set y₁ a₁ = outer.set y a₁ := by simp [y₁]
    rw [hset] at h1
    exact h1.tail h2

instance (priority := low) FactorsLawful.ofLawful {s : Type u} {a : Type v}
    (l : Lens s a) [LawfulLens l] : FactorsLawful l where
  set_get := Lens.set_get l
  rev _ _ h := ReflTransGen.single h.symm

instance FactorsLawful.prod {s : Type u} {a : Type v} {b : Type w}
    (l₁ : Lens s a) (l₂ : Lens s b) [h₁ : FactorsLawful l₁] [h₂ : FactorsLawful l₂] :
    FactorsLawful (l₁.prod l₂) where
  set_get x := by
    change l₂.set (l₁.set x (l₁.get x)) (l₂.get x) = x
    rw [h₁.set_get, h₂.set_get]
  rev x y h := by
    rcases Modifies.prod_iff_exists.mp h with ⟨mid, hm₁, hm₂⟩
    have hrev₁ : ReflTransGen (Modifies (l₁.prod l₂)) y mid :=
      (h₁.rev mid y hm₁).mono (fun _ _ => Modifies.prod_left_of_set_get l₂ h₂.set_get)
    have hrev₂ : ReflTransGen (Modifies (l₁.prod l₂)) mid x :=
      (h₂.rev x mid hm₂).mono (fun _ _ => Modifies.prod_right_of_set_get l₁ h₁.set_get)
    exact hrev₁.trans hrev₂

instance FactorsLawful.comp {s : Type u} {a : Type v} {b : Type w}
    (outer : Lens s a) (inner : Lens a b) [LawfulLens outer] [h : FactorsLawful inner] :
    FactorsLawful (outer.comp inner) where
  set_get x := by
    change outer.set x (inner.set (outer.get x) (inner.get (outer.get x))) = x
    rw [h.set_get, Lens.set_get]
  rev x y hm := by
    rcases hm with ⟨v, rfl⟩
    let a' := inner.set (outer.get y) v
    have hrev : ReflTransGen (Modifies inner) (outer.get y) a' :=
      h.rev a' (outer.get y) ⟨v, rfl⟩
    have hlifted := Modifies.rt_lift outer (x := outer.set y a') (by simpa [a'] using hrev)
    simpa [a'] using hlifted

namespace Modifies

theorem refl_prod {s : Type u} {a : Type v} {b : Type w}
    (l₁ : Lens s a) (l₂ : Lens s b) [FactorsLawful l₁] [FactorsLawful l₂] (x : s) :
    Modifies (l₁.prod l₂) x x :=
  refl_of_factorsLawful (l₁.prod l₂) x

theorem prod_left {s : Type u} {a : Type v} {b : Type w}
    {l₁ : Lens s a} (l₂ : Lens s b) [h₂ : FactorsLawful l₂] {s' s₀ : s}
    (h : Modifies l₁ s' s₀) :
    Modifies (l₁.prod l₂) s' s₀ :=
  prod_left_of_set_get l₂ h₂.set_get h

theorem prod_right {s : Type u} {a : Type v} {b : Type w}
    (l₁ : Lens s a) {l₂ : Lens s b} [h₁ : FactorsLawful l₁] {s' s₀ : s}
    (h : Modifies l₂ s' s₀) :
    Modifies (l₁.prod l₂) s' s₀ :=
  prod_right_of_set_get l₁ h₁.set_get h

/-! #### Duplicates and Subsumed Overlaps (Single-Pass) -/

theorem prod_dup_iff {s : Type u} {a : Type v} {l : Lens s a} [LawfulLens l] {s' s₀ : s} :
    Modifies (l.prod l) s' s₀ ↔ Modifies l s' s₀ := by
  constructor
  · rintro ⟨⟨v₁, v₂⟩, rfl⟩
    exact ⟨v₂, by simp⟩
  · exact prod_left l

theorem prod_comp_left_iff {s : Type u} {a : Type v} {b : Type w}
    {outer : Lens s a} {inner : Lens a b} [LawfulLens outer] [LawfulLens inner] {s' s₀ : s} :
    Modifies ((outer.comp inner).prod outer) s' s₀ ↔ Modifies outer s' s₀ := by
  constructor
  · rintro ⟨⟨v₁, v₂⟩, rfl⟩
    exact ⟨v₂, by simp⟩
  · exact prod_right (outer.comp inner)

theorem prod_comp_right_iff {s : Type u} {a : Type v} {b : Type w}
    {outer : Lens s a} {inner : Lens a b} [LawfulLens outer] [LawfulLens inner] {s' s₀ : s} :
    Modifies (outer.prod (outer.comp inner)) s' s₀ ↔ Modifies outer s' s₀ := by
  constructor
  · rintro ⟨⟨v₁, v₂⟩, rfl⟩
    exact ⟨inner.set v₁ v₂, by simp⟩
  · exact prod_left (outer.comp inner)

/-! ### Reflexive-Transitive Closure Theory (`ReflTransGen (Modifies l)`) -/

theorem rt_single {s : Type u} {a : Type v} {l : Lens s a} {s' s₀ : s}
    (h : Modifies l s' s₀) : ReflTransGen (Modifies l) s' s₀ :=
  ReflTransGen.single h

theorem rt_set {s : Type u} {a : Type v} (l : Lens s a) (x : s) (v : a) :
    ReflTransGen (Modifies l) (l.set x v) x :=
  rt_single (set l x v)

theorem rt_over {s : Type u} {a : Type v} (l : Lens s a) (f : a → a) (x : s) :
    ReflTransGen (Modifies l) (l.over f x) x :=
  rt_single (over l f x)

/-- Unconditional symmetry of `ReflTransGen (Modifies l)` whenever `FactorsLawful l` holds
(no `Disjoint` proof required for product lenses). -/
theorem rt_symm {s : Type u} {a : Type v} {l : Lens s a} [h : FactorsLawful l] {s' s₀ : s}
    (hm : ReflTransGen (Modifies l) s' s₀) : ReflTransGen (Modifies l) s₀ s' :=
  hm.symm_of_rev h.rev

/-- When `l` is itself a `LawfulLens`, `ReflTransGen (Modifies l)` collapses to `Modifies l`. -/
theorem rt_iff_of_lawful {s : Type u} {a : Type v} {l : Lens s a} [LawfulLens l] {s' s₀ : s} :
    ReflTransGen (Modifies l) s' s₀ ↔ Modifies l s' s₀ :=
  ⟨ReflTransGen.of_refl_trans (refl l) (fun a b => comp b a) (fun _ _ h => h), rt_single⟩

theorem rt_unit_iff {s : Type u} {s' s₀ : s} :
    ReflTransGen (Modifies (Lens.unit.{u, v} (s := s))) s' s₀ ↔ s' = s₀ := by
  rw [rt_iff_of_lawful, unit_iff]

theorem rt_prod_unit_left_iff {s : Type u} {a : Type v} {l : Lens s a} {s' s₀ : s} :
    ReflTransGen (Modifies ((Lens.unit.{u, w} (s := s)).prod l)) s' s₀ ↔
      ReflTransGen (Modifies l) s' s₀ :=
  ⟨ReflTransGen.mono (fun _ _ => prod_unit_left_iff.mp),
   ReflTransGen.mono (fun _ _ => prod_unit_left_iff.mpr)⟩

theorem rt_prod_unit_right_iff {s : Type u} {a : Type v} {l : Lens s a} {s' s₀ : s} :
    ReflTransGen (Modifies (l.prod (Lens.unit.{u, w} (s := s)))) s' s₀ ↔
      ReflTransGen (Modifies l) s' s₀ :=
  ⟨ReflTransGen.mono (fun _ _ => prod_unit_right_iff.mp),
   ReflTransGen.mono (fun _ _ => prod_unit_right_iff.mpr)⟩

theorem rt_prod_left {s : Type u} {a : Type v} {b : Type w}
    {l₁ : Lens s a} (l₂ : Lens s b) [FactorsLawful l₂] {s' s₀ : s}
    (h : ReflTransGen (Modifies l₁) s' s₀) :
    ReflTransGen (Modifies (l₁.prod l₂)) s' s₀ :=
  h.mono (fun _ _ => prod_left l₂)

theorem rt_prod_right {s : Type u} {a : Type v} {b : Type w}
    (l₁ : Lens s a) {l₂ : Lens s b} [FactorsLawful l₁] {s' s₀ : s}
    (h : ReflTransGen (Modifies l₂) s' s₀) :
    ReflTransGen (Modifies (l₁.prod l₂)) s' s₀ :=
  h.mono (fun _ _ => prod_right l₁)

theorem rt_prod_comp {s : Type u} {a : Type v} {b : Type w}
    {l₁ : Lens s a} {l₂ : Lens s b} [FactorsLawful l₁] [FactorsLawful l₂] {s₁ s₂ s₃ : s}
    (h₁ : ReflTransGen (Modifies l₁) s₂ s₁) (h₂ : ReflTransGen (Modifies l₂) s₃ s₂) :
    ReflTransGen (Modifies (l₁.prod l₂)) s₃ s₁ :=
  (rt_prod_right l₁ h₂).trans (rt_prod_left l₂ h₁)

theorem rt_prod_assoc_iff {s : Type u} {a : Type v} {b : Type w} {c : Type u₁}
    {l₁ : Lens s a} {l₂ : Lens s b} {l₃ : Lens s c} {s' s₀ : s} :
    ReflTransGen (Modifies ((l₁.prod l₂).prod l₃)) s' s₀ ↔
      ReflTransGen (Modifies (l₁.prod (l₂.prod l₃))) s' s₀ :=
  ⟨ReflTransGen.mono (fun _ _ => prod_assoc.mp),
   ReflTransGen.mono (fun _ _ => prod_assoc.mpr)⟩

/-- Unconditional commutativity (one direction) of `ReflTransGen (Modifies (l₁ ×ₗ l₂))` without `Disjoint`. -/
theorem rt_prod_comm {s : Type u} {a : Type v} {b : Type w}
    {l₁ : Lens s a} {l₂ : Lens s b} [FactorsLawful l₁] [FactorsLawful l₂] {s' s₀ : s}
    (h : ReflTransGen (Modifies (l₁.prod l₂)) s' s₀) :
    ReflTransGen (Modifies (l₂.prod l₁)) s' s₀ := by
  refine h.mono_rt (fun _ _ huv => ?_)
  rcases prod_iff_exists.mp huv with ⟨mid, hm₁, hm₂⟩
  exact (rt_single (prod_left l₁ hm₂)).trans (rt_single (prod_right l₂ hm₁))

/-- Unconditional commutativity of `ReflTransGen (Modifies (l₁ ×ₗ l₂))` without `Disjoint`. -/
theorem rt_prod_comm_iff {s : Type u} {a : Type v} {b : Type w}
    {l₁ : Lens s a} {l₂ : Lens s b} [FactorsLawful l₁] [FactorsLawful l₂] {s' s₀ : s} :
    ReflTransGen (Modifies (l₁.prod l₂)) s' s₀ ↔ ReflTransGen (Modifies (l₂.prod l₁)) s' s₀ :=
  ⟨rt_prod_comm, rt_prod_comm⟩

theorem rt_prod_mono_left {s : Type u} {a : Type v} {a' : Type u₁} {b : Type w}
    {l₁ : Lens s a} {l₁' : Lens s a'} {l₂ : Lens s b} [FactorsLawful l₁'] [FactorsLawful l₂]
    (hsub : ∀ x y : s, ReflTransGen (Modifies l₁) x y → ReflTransGen (Modifies l₁') x y)
    {s' s₀ : s} (h : ReflTransGen (Modifies (l₁.prod l₂)) s' s₀) :
    ReflTransGen (Modifies (l₁'.prod l₂)) s' s₀ := by
  refine h.mono_rt (fun _ _ hab => ?_)
  rcases prod_iff_exists.mp hab with ⟨mid, hm₁, hm₂⟩
  exact (rt_single (prod_right l₁' hm₂)).trans (rt_prod_left l₂ (hsub mid _ (rt_single hm₁)))

theorem rt_prod_mono_right {s : Type u} {a : Type v} {b : Type w} {b' : Type u₁}
    {l₁ : Lens s a} {l₂ : Lens s b} {l₂' : Lens s b'} [FactorsLawful l₁] [FactorsLawful l₂]
    [FactorsLawful l₂']
    (hsub : ∀ x y : s, ReflTransGen (Modifies l₂) x y → ReflTransGen (Modifies l₂') x y)
    {s' s₀ : s} (h : ReflTransGen (Modifies (l₁.prod l₂)) s' s₀) :
    ReflTransGen (Modifies (l₁.prod l₂')) s' s₀ :=
  rt_prod_comm (rt_prod_mono_left hsub (rt_prod_comm h))

theorem rt_prod_congr_left {s : Type u} {a : Type v} {a' : Type u₁} {b : Type w}
    {l₁ : Lens s a} {l₁' : Lens s a'} {l₂ : Lens s b} [FactorsLawful l₁] [FactorsLawful l₁']
    [FactorsLawful l₂] {s' s₀ : s}
    (heq : ∀ x y : s, ReflTransGen (Modifies l₁) x y ↔ ReflTransGen (Modifies l₁') x y) :
    ReflTransGen (Modifies (l₁.prod l₂)) s' s₀ ↔ ReflTransGen (Modifies (l₁'.prod l₂)) s' s₀ :=
  ⟨rt_prod_mono_left (fun x y => (heq x y).mp), rt_prod_mono_left (fun x y => (heq x y).mpr)⟩

theorem rt_prod_congr_right {s : Type u} {a : Type v} {b : Type w} {b' : Type u₁}
    {l₁ : Lens s a} {l₂ : Lens s b} {l₂' : Lens s b'} [FactorsLawful l₁] [FactorsLawful l₂]
    [FactorsLawful l₂'] {s' s₀ : s}
    (heq : ∀ x y : s, ReflTransGen (Modifies l₂) x y ↔ ReflTransGen (Modifies l₂') x y) :
    ReflTransGen (Modifies (l₁.prod l₂)) s' s₀ ↔ ReflTransGen (Modifies (l₁.prod l₂')) s' s₀ :=
  ⟨rt_prod_mono_right (fun x y => (heq x y).mp), rt_prod_mono_right (fun x y => (heq x y).mpr)⟩

/-- Duplicate absorption holds for arbitrary `FactorsLawful` lenses (even non-disjoint products). -/
theorem rt_prod_dup_iff {s : Type u} {a : Type v} {l : Lens s a} [FactorsLawful l] {s' s₀ : s} :
    ReflTransGen (Modifies (l.prod l)) s' s₀ ↔ ReflTransGen (Modifies l) s' s₀ := by
  constructor
  · refine ReflTransGen.mono_rt (fun _ _ h => ?_)
    rcases prod_iff_exists.mp h with ⟨_, h₁, h₂⟩
    exact (rt_single h₂).trans (rt_single h₁)
  · exact rt_prod_left l

theorem rt_coarsen {s : Type u} {a : Type v} {b : Type w}
    {outer : Lens s a} {inner : Lens a b} {s' s₀ : s}
    (h : ReflTransGen (Modifies (outer.comp inner)) s' s₀) :
    ReflTransGen (Modifies outer) s' s₀ :=
  h.mono (fun _ _ => coarsen)

theorem rt_prod_comp_left_iff {s : Type u} {a : Type v} {b : Type w}
    {outer : Lens s a} {inner : Lens a b} [LawfulLens outer] [FactorsLawful inner] {s' s₀ : s} :
    ReflTransGen (Modifies ((outer.comp inner).prod outer)) s' s₀ ↔
      ReflTransGen (Modifies outer) s' s₀ := by
  constructor
  · refine ReflTransGen.mono_rt (fun _ _ h => ?_)
    rcases prod_iff_exists.mp h with ⟨_, h₁, h₂⟩
    exact (rt_single h₂).trans (rt_single (coarsen h₁))
  · exact rt_prod_right (outer.comp inner)

theorem rt_prod_comp_right_iff {s : Type u} {a : Type v} {b : Type w}
    {outer : Lens s a} {inner : Lens a b} [LawfulLens outer] [FactorsLawful inner] {s' s₀ : s} :
    ReflTransGen (Modifies (outer.prod (outer.comp inner))) s' s₀ ↔
      ReflTransGen (Modifies outer) s' s₀ := by
  rw [rt_prod_comm_iff, rt_prod_comp_left_iff]

/-- Characterization of getter preservation across `ReflTransGen (Modifies l)`. -/
theorem rt_preserves_iff {s : Type u} {a : Type v} {b : Type w}
    {l : Lens s a} {g : Getter s b} :
    (∀ s' s, ReflTransGen (Modifies l) s' s → g.get s' = g.get s) ↔ Independent l g := by
  rw [ReflTransGen.preserves_iff]
  constructor
  · intro h x v
    exact h (l.set x v) x ⟨v, rfl⟩
  · intro hind _ _ hm
    exact preserves hind hm

/-- Any `Getter` independent of `l` is preserved across `ReflTransGen (Modifies l)`. -/
theorem rt_preserves {s : Type u} {a : Type v} {b : Type w}
    {l : Lens s a} {g : Getter s b} {s' s₀ : s}
    (hind : Independent l g) (h : ReflTransGen (Modifies l) s' s₀) :
    g.get s' = g.get s₀ :=
  rt_preserves_iff.mpr hind s' s₀ h

/-- Any lawful `Lens` disjoint from `l` is preserved across `ReflTransGen (Modifies l)`. -/
theorem rt_preserves_disjoint {s : Type u} {a : Type v} {b : Type w}
    {l : Lens s a} {k : Lens s b} [LawfulLens k] {s' s₀ : s}
    (hdisj : Disjoint l k) (h : ReflTransGen (Modifies l) s' s₀) :
    k.get s' = k.get s₀ :=
  rt_preserves hdisj.independent_left h

/-- Narrow `ReflTransGen (Modifies l)` into `EqOnAll gs`. -/
theorem rt_preserves_all {s : Type u} {a : Type v} {l : Lens s a}
    {gs : List (AnyGetter.{u, w} s)} {s' s₀ : s}
    (hind : ∀ g ∈ gs, Independent l g.getter)
    (h : ReflTransGen (Modifies l) s' s₀) :
    EqOnAll gs s' s₀ :=
  fun g hg => rt_preserves (hind g hg) h

theorem rt_comp_prod_iff {s : Type u} {a : Type v} {b : Type w} {c : Type u₁}
    (outer : Lens s a) [LawfulLens outer] {inner₁ : Lens a b} {inner₂ : Lens a c} {s' s₀ : s} :
    ReflTransGen (Modifies (outer.comp (inner₁.prod inner₂))) s' s₀ ↔
      ReflTransGen (Modifies ((outer.comp inner₁).prod (outer.comp inner₂))) s' s₀ :=
  ⟨ReflTransGen.mono (fun _ _ => (comp_prod_iff outer).mp),
   ReflTransGen.mono (fun _ _ => (comp_prod_iff outer).mpr)⟩

theorem rt_lift_prod {s : Type u} {a : Type v} {b : Type w} {c : Type u₁}
    (outer : Lens s a) [LawfulLens outer] {inner₁ : Lens a b} {inner₂ : Lens a c}
    {x : s} {a' : a} (h : ReflTransGen (Modifies (inner₁.prod inner₂)) a' (outer.get x)) :
    ReflTransGen (Modifies ((outer.comp inner₁).prod (outer.comp inner₂))) (outer.set x a') x :=
  (rt_comp_prod_iff outer).mp (rt_lift outer h)

theorem rt_lift_unit {s : Type u} {a : Type v}
    (outer : Lens s a) [LawfulLens outer] {x : s} {a' : a}
    (h : ReflTransGen (Modifies (Lens.unit.{v, w} (s := a))) a' (outer.get x)) :
    ReflTransGen (Modifies (Lens.unit.{u, w} (s := s))) (outer.set x a') x := by
  rw [rt_unit_iff] at h ⊢
  rw [h, Lens.set_get]

/-- Equivalence between `ReflTransGen (Modifies (l₁ ×ₗ l₂))` and `ModifiesAny [l₁, l₂]`
whenever both factors satisfy `FactorsLawful` (no `Disjoint` required). -/
theorem rt_prod_iff_modifiesAny {s : Type u} {a b : Type v}
    {l₁ : Lens s a} {l₂ : Lens s b} [FactorsLawful l₁] [FactorsLawful l₂] {s' s₀ : s} :
    ReflTransGen (Modifies (l₁.prod l₂)) s' s₀ ↔
      ModifiesAny [AnyLens.of l₁, AnyLens.of l₂] s' s₀ := by
  constructor
  · refine ReflTransGen.of_refl_trans ModifiesAny.refl (fun a b => ModifiesAny.comp b a) ?_
    intro x y h
    rcases prod_iff_exists.mp h with ⟨mid, h₁, h₂⟩
    exact ModifiesAny.step (List.mem_cons_self ..) h₁
      (ModifiesAny.single (List.mem_cons_of_mem _ (List.mem_cons_self ..)) h₂)
  · intro h
    induction h with
    | refl => exact .refl
    | step hmem hmod _ ih =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · exact ih.tail (prod_left l₂ hmod)
      · exact ih.tail (prod_right l₁ hmod)

end Modifies

end Optic

end
