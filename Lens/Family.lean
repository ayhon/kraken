module

public import Lens.Basic
public import Lens.Frame
public import Lens.ProdFrame

/-!
# Indexed Lens Families (`LensFamily`, `LawfulLensFamily`) and Bridge Theorems

Optional layer on top of `Lens.Frame` and `Lens.ProdFrame` for dynamically indexed state
(e.g., runtime register names `r : XReg` or memory addresses `a : BitVec 64`).

Provides `LensFamily`, `LawfulLensFamily`, and the bridge theorems showing that
`ModifiesAny`, `Modifies (F.prodLens W)`, and `ReflTransGen (Modifies (F.prodLens W))` are
equivalent to pointwise agreement outside a write set `W`
(`∀ i ∉ W, (F.lens i).get s' = (F.lens i).get s`), recovering `Kraken.RegFile.EqExcept` as a
special case without requiring `ι` to be finite.
-/

@[expose] public section

namespace Optic

universe u v w

/-! ### Indexed Lens Families -/

/-- A family of lenses on `s` indexed by `ι`, with potentially index-dependent field types `α i`.
Covers homogeneous register files (`α := fun _ => UInt64`), heterogeneous structs, and
infinite maps alike. -/
structure LensFamily (s : Type u) (ι : Type v) (α : ι → Type w) where
  lens : (i : ι) → Lens s (α i)

/-- A `LensFamily` is lawful and complete if every member is a lawful lens, distinct indices
are pairwise disjoint, and the family jointly determines `s` (extensionality). -/
class LawfulLensFamily {s : Type u} {ι : Type v} {α : ι → Type w}
    (F : LensFamily s ι α) : Prop where
  lawful : ∀ i, LawfulLens (F.lens i)
  disjoint : ∀ i j, i ≠ j → Disjoint (F.lens i) (F.lens j)
  ext : ∀ s₁ s₂ : s, (∀ i, (F.lens i).get s₁ = (F.lens i).get s₂) → s₁ = s₂

/-! ### Helpers for `ProdFrame` -/

namespace LensFamily

/-- Right-associated tuple focus type for a finite list of indices `W` in a `LensFamily`. -/
def ProdType {ι : Type v} (α : ι → Type w) : List ι → Type w
  | [] => PUnit.{w + 1}
  | [i] => α i
  | i :: j :: rest => α i × ProdType α (j :: rest)

/-- Right-associated product lens over a finite list of indices `W`. -/
def prodLens {s : Type u} {ι : Type v} {α : ι → Type w}
    (F : LensFamily s ι α) : (W : List ι) → Lens s (ProdType α W)
  | [] => Lens.unit
  | [i] => F.lens i
  | i :: j :: rest => (F.lens i).prod (F.prodLens (j :: rest))

end LensFamily

/-! ### Bridge Theorems -/

namespace LawfulLensFamily

private def patch {s : Type u} {ι : Type v} {α : ι → Type w}
    (F : LensFamily s ι α) (target : s) : List ι → s → s
  | [], acc => acc
  | j :: js, acc => patch F target js ((F.lens j).set acc ((F.lens j).get target))

private theorem get_patch_of_not_mem {s : Type u} {ι : Type v} {α : ι → Type w}
    (F : LensFamily s ι α) [LawfulLensFamily F] (target : s) (W : List ι) (acc : s)
    (i : ι) (hi : i ∉ W) :
    (F.lens i).get (patch F target W acc) = (F.lens i).get acc := by
  induction W generalizing acc with
  | nil => rfl
  | cons j js ih =>
    have hne : j ≠ i := fun h => hi (h ▸ List.mem_cons_self ..)
    have hi' : i ∉ js := fun h => hi (List.mem_cons_of_mem _ h)
    haveI := LawfulLensFamily.lawful (F := F) i
    simp only [patch]
    rw [ih _ hi', (LawfulLensFamily.disjoint (F := F) j i hne).get₂_set₁]

private theorem get_patch_of_mem {s : Type u} {ι : Type v} {α : ι → Type w} [DecidableEq ι]
    (F : LensFamily s ι α) [LawfulLensFamily F] (target : s) (W : List ι) (acc : s)
    (i : ι) (hi : i ∈ W) :
    (F.lens i).get (patch F target W acc) = (F.lens i).get target := by
  induction W generalizing acc with
  | nil => cases hi
  | cons j js ih =>
    simp only [patch]
    by_cases hmem : i ∈ js
    · exact ih _ hmem
    · have hij : i = j := by
        cases hi with
        | head => rfl
        | tail _ h => exact absurd h hmem
      subst hij
      rw [get_patch_of_not_mem F target js _ i hmem]
      haveI := LawfulLensFamily.lawful (F := F) i
      exact Lens.get_set (F.lens i) acc ((F.lens i).get target)

private theorem patch_eq {s : Type u} {ι : Type v} {α : ι → Type w} [DecidableEq ι]
    (F : LensFamily s ι α) [LawfulLensFamily F] (W : List ι) {s' s : s}
    (h : ∀ i, i ∉ W → (F.lens i).get s' = (F.lens i).get s) :
    patch F s' W s = s' := by
  apply LawfulLensFamily.ext (F := F)
  intro i
  by_cases hi : i ∈ W
  · exact get_patch_of_mem F s' W s i hi
  · rw [get_patch_of_not_mem F s' W s i hi, h i hi]

/-! #### 1. Baseline (`ModifiesAny`) Bridge -/

private theorem modifiesAny_patch {s : Type u} {ι : Type v} {α : ι → Type w}
    (F : LensFamily s ι α) (target : s) (W : List ι) (acc : s) :
    ModifiesAny (W.map fun i => AnyLens.of (F.lens i)) (patch F target W acc) acc := by
  induction W generalizing acc with
  | nil => exact ModifiesAny.refl acc
  | cons j js ih =>
    simp only [patch, List.map_cons]
    have hstep : Modifies (F.lens j) ((F.lens j).set acc ((F.lens j).get target)) acc :=
      Modifies.set (F.lens j) acc ((F.lens j).get target)
    have hrest := ModifiesAny.mono
      (fun _ hm => List.mem_cons_of_mem (AnyLens.of (F.lens j)) hm)
      (ih ((F.lens j).set acc ((F.lens j).get target)))
    exact ModifiesAny.step (List.mem_cons_self ..) hstep hrest

theorem modifiesAny_iff {s : Type u} {ι : Type v} {α : ι → Type w} [DecidableEq ι]
    (F : LensFamily s ι α) [LawfulLensFamily F] (W : List ι) (s' s : s) :
    ModifiesAny (W.map fun i => AnyLens.of (F.lens i)) s' s ↔
      ∀ i, i ∉ W → (F.lens i).get s' = (F.lens i).get s := by
  constructor
  · intro h i hi
    refine ModifiesAny.preserves (g := (F.lens i).toGetter) ?_ h
    intro l hl
    rcases List.mem_map.mp hl with ⟨j, hj, rfl⟩
    have hne : j ≠ i := fun heq => hi (heq ▸ hj)
    haveI := LawfulLensFamily.lawful (F := F) i
    exact (LawfulLensFamily.disjoint (F := F) j i hne).independent_left
  · intro h
    have hpatch := modifiesAny_patch F s' W s
    rwa [patch_eq F W h] at hpatch

/-! #### 2. Product-Lens (`F.prodLens W`) and `ReflTransGen` Bridges -/

theorem disjoint_prodLens {s : Type u} {ι : Type v} {α : ι → Type w}
    (F : LensFamily s ι α) [LawfulLensFamily F] (W : List ι) (i : ι) (hi : i ∉ W) :
    Disjoint (F.prodLens W) (F.lens i) := by
  match W with
  | [] => exact Disjoint.unit_left _
  | [j] =>
    have hne : j ≠ i := fun h => hi (h ▸ List.mem_cons_self ..)
    exact LawfulLensFamily.disjoint j i hne
  | j :: k :: rest =>
    have hne : j ≠ i := fun h => hi (h ▸ List.mem_cons_self ..)
    have hi' : i ∉ k :: rest := fun h => hi (List.mem_cons_of_mem _ h)
    exact Disjoint.prod_left (LawfulLensFamily.disjoint j i hne) (disjoint_prodLens F (k :: rest) i hi')

theorem independent_prodLens {s : Type u} {ι : Type v} {α : ι → Type w}
    (F : LensFamily s ι α) [LawfulLensFamily F] (W : List ι) (i : ι) (hi : i ∉ W) :
    Independent (F.prodLens W) (F.lens i).toGetter := by
  haveI := LawfulLensFamily.lawful (F := F) i
  exact (disjoint_prodLens F W i hi).independent_left

theorem factorsLawful_prodLens {s : Type u} {ι : Type v} {α : ι → Type w}
    (F : LensFamily s ι α) [LawfulLensFamily F] (W : List ι) :
    FactorsLawful (F.prodLens W) := by
  match W with
  | [] => exact FactorsLawful.ofLawful Lens.unit
  | [j] =>
    haveI := LawfulLensFamily.lawful (F := F) j
    exact FactorsLawful.ofLawful (F.lens j)
  | j :: k :: rest =>
    haveI := LawfulLensFamily.lawful (F := F) j
    haveI := factorsLawful_prodLens F (k :: rest)
    exact FactorsLawful.prod (F.lens j) (F.prodLens (k :: rest))

theorem lawful_prodLens {s : Type u} {ι : Type v} {α : ι → Type w}
    (F : LensFamily s ι α) [LawfulLensFamily F] (W : List ι) (hnd : W.Nodup) :
    LawfulLens (F.prodLens W) := by
  match W with
  | [] => exact Lens.lawful_unit
  | [j] => exact LawfulLensFamily.lawful j
  | j :: k :: rest =>
    rw [List.nodup_cons] at hnd
    haveI := LawfulLensFamily.lawful (F := F) j
    haveI := lawful_prodLens F (k :: rest) hnd.2
    exact Lens.lawful_prod (F.lens j) (F.prodLens (k :: rest))
      (disjoint_prodLens F (k :: rest) j hnd.1).symm

private theorem get_prodLens_set_of_mem {s : Type u} {ι : Type v} {α : ι → Type w} [DecidableEq ι]
    (F : LensFamily s ι α) [LawfulLensFamily F] (target : s) (W : List ι) (acc : s)
    (i : ι) (hi : i ∈ W) :
    (F.lens i).get ((F.prodLens W).set acc ((F.prodLens W).get target)) = (F.lens i).get target := by
  match W with
  | [] => cases hi
  | [j] =>
    simp only [List.mem_singleton] at hi
    subst hi
    haveI := LawfulLensFamily.lawful (F := F) i
    exact Lens.get_set (F.lens i) acc ((F.lens i).get target)
  | j :: k :: rest =>
    simp only [LensFamily.prodLens, Lens.prod]
    by_cases hmem : i ∈ k :: rest
    · exact get_prodLens_set_of_mem F target (k :: rest) _ i hmem
    · have hij : i = j := by
        cases hi with
        | head => rfl
        | tail _ h => exact absurd h hmem
      subst hij
      haveI := LawfulLensFamily.lawful (F := F) i
      rw [(disjoint_prodLens F (k :: rest) i hmem).get₂_set₁]
      exact Lens.get_set (F.lens i) acc ((F.lens i).get target)

theorem modifies_prodLens_iff {s : Type u} {ι : Type v} {α : ι → Type w} [DecidableEq ι]
    (F : LensFamily s ι α) [LawfulLensFamily F] (W : List ι) (s' s : s) :
    Modifies (F.prodLens W) s' s ↔
      ∀ i, i ∉ W → (F.lens i).get s' = (F.lens i).get s := by
  constructor
  · intro h i hi
    exact Modifies.preserves (independent_prodLens F W i hi) h
  · intro h
    refine ⟨(F.prodLens W).get s', ?_⟩
    apply LawfulLensFamily.ext (F := F)
    intro i
    by_cases hi : i ∈ W
    · exact (get_prodLens_set_of_mem F s' W s i hi).symm
    · haveI := LawfulLensFamily.lawful (F := F) i
      rw [(disjoint_prodLens F W i hi).get₂_set₁, h i hi]

theorem rt_modifies_prodLens_iff {s : Type u} {ι : Type v} {α : ι → Type w} [DecidableEq ι]
    (F : LensFamily s ι α) [LawfulLensFamily F] (W : List ι) (s' s : s) :
    ReflTransGen (Modifies (F.prodLens W)) s' s ↔
      ∀ i, i ∉ W → (F.lens i).get s' = (F.lens i).get s :=
  ⟨fun h i hi => Modifies.rt_preserves (independent_prodLens F W i hi) h,
   fun h => ReflTransGen.single ((modifies_prodLens_iff F W s' s).mpr h)⟩

end LawfulLensFamily

end Optic

end
