module

/-!
# Reflexive-Transitive Closure (`ReflTransGen`)

Standalone, zero-dependency reflexive-transitive closure modeled on Mathlib's
`Relation.ReflTransGen`.

Naming convention:
- `trans` follows relational order: `R a b → R b c → R a c` (with a `Trans` instance).
- `comp` follows reverse / state-update order: `R b c → R a b → R a c`.
-/

@[expose] public section

namespace Optic

universe u v

/-- The reflexive-transitive closure of a binary relation `r : α → α → Prop`. -/
inductive ReflTransGen {α : Type u} (r : α → α → Prop) (a : α) : α → Prop
  | refl : ReflTransGen r a a
  | tail {b c : α} : ReflTransGen r a b → r b c → ReflTransGen r a c

namespace ReflTransGen

variable {α : Type u} {β : Type v} {r q : α → α → Prop} {a b c : α}

/-- Embed a single `r`-step into `ReflTransGen r`. -/
theorem single (h : r a b) : ReflTransGen r a b :=
  .tail .refl h

/-- Relational transitivity: `ReflTransGen r a b → ReflTransGen r b c → ReflTransGen r a c`. -/
theorem trans (hab : ReflTransGen r a b) (hbc : ReflTransGen r b c) : ReflTransGen r a c := by
  induction hbc with
  | refl => exact hab
  | tail _ h ih => exact .tail ih h

instance : Trans (ReflTransGen r) (ReflTransGen r) (ReflTransGen r) where
  trans := ReflTransGen.trans

/-- Reverse-order composition (matching `Modifies.comp` / `EqOn.comp`). -/
theorem comp (h₁ : ReflTransGen r b c) (h₂ : ReflTransGen r a b) : ReflTransGen r a c :=
  trans h₂ h₁

/-- Prepend a single `r`-step on the left. -/
theorem head (hab : r a b) (hbc : ReflTransGen r b c) : ReflTransGen r a c :=
  trans (single hab) hbc

/-- Case split on the first step from the left. -/
theorem cases_head (h : ReflTransGen r a c) : a = c ∨ ∃ b, r a b ∧ ReflTransGen r b c := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hbc ih =>
    rcases ih with rfl | ⟨d, had, hdb⟩
    · exact Or.inr ⟨_, hbc, .refl⟩
    · exact Or.inr ⟨d, had, hdb.tail hbc⟩

/-- Case split on the last step on the right. -/
theorem cases_tail (h : ReflTransGen r a c) : a = c ∨ ∃ b, ReflTransGen r a b ∧ r b c := by
  cases h with
  | refl => exact Or.inl rfl
  | tail hab hbc => exact Or.inr ⟨_, hab, hbc⟩

/-- Induction principle peeling steps from the left (`head`). -/
theorem head_induction_on {P : ∀ a, ReflTransGen r a c → Prop}
    {a : α} (h : ReflTransGen r a c)
    (refl : P c .refl)
    (head : ∀ {a b} (hab : r a b) (hbc : ReflTransGen r b c), P b hbc → P a (head hab hbc)) :
    P a h := by
  suffices ∀ {x y} (hxy : ReflTransGen r x y) (hyc : ReflTransGen r y c),
      P y hyc → P x (hxy.trans hyc) from
    this h .refl refl
  intro x y hxy
  induction hxy with
  | refl =>
    intro hyc hP
    exact hP
  | @tail u v hxu huv ih =>
    intro hvc hP
    exact ih (ReflTransGen.head huv hvc) (head huv hvc hP)

/-- Induction into any reflexive-transitive relation `q` containing `r`. -/
theorem of_refl_trans
    (hrefl : ∀ x, q x x)
    (htrans : ∀ {x y z}, q x y → q y z → q x z)
    (hsub : ∀ x y, r x y → q x y)
    (h : ReflTransGen r a b) : q a b := by
  induction h with
  | refl => exact hrefl a
  | tail _ hstep ih => exact htrans ih (hsub _ _ hstep)

/-- Monotonicity: if `r ⊆ q` then `ReflTransGen r ⊆ ReflTransGen q`. -/
theorem mono (hsub : ∀ x y, r x y → q x y) (h : ReflTransGen r a b) : ReflTransGen q a b :=
  of_refl_trans (fun _ => .refl) trans (fun x y hxy => single (hsub x y hxy)) h

/-- Stronger monotonicity: if `r ⊆ ReflTransGen q` then `ReflTransGen r ⊆ ReflTransGen q`. -/
theorem mono_rt (hsub : ∀ x y, r x y → ReflTransGen q x y) (h : ReflTransGen r a b) :
    ReflTransGen q a b :=
  of_refl_trans (fun _ => .refl) trans hsub h

/-- Map a `ReflTransGen` derivation through a function `f : α → β`. -/
theorem lift {q : β → β → Prop} (f : α → β)
    (hf : ∀ x y, r x y → q (f x) (f y))
    (h : ReflTransGen r a b) : ReflTransGen q (f a) (f b) :=
  of_refl_trans (q := fun x y => ReflTransGen q (f x) (f y))
    (fun _ => .refl) trans (fun x y hxy => single (hf x y hxy)) h

/-- Symmetry whenever every single `r`-step can be reversed in `ReflTransGen r`. -/
theorem symm_of_rev (hrev : ∀ x y, r x y → ReflTransGen r y x)
    (h : ReflTransGen r a b) : ReflTransGen r b a :=
  of_refl_trans (q := fun x y => ReflTransGen r y x)
    (fun _ => .refl) (fun h1 h2 => h2.trans h1) hrev h

/-- Symmetry whenever `r` itself is symmetric. -/
theorem symmetric (hsymm : ∀ x y, r x y → r y x)
    (h : ReflTransGen r a b) : ReflTransGen r b a :=
  symm_of_rev (fun x y hxy => single (hsymm x y hxy)) h

/-- Idempotence of reflexive-transitive closure. -/
theorem idem_iff : ReflTransGen (ReflTransGen r) a b ↔ ReflTransGen r a b :=
  ⟨mono_rt (fun _ _ h => h), single⟩

/-- Reflexive-transitive closure of `Eq` is `Eq`. -/
theorem eq_iff : ReflTransGen Eq a b ↔ a = b :=
  ⟨of_refl_trans (fun _ => rfl) Eq.trans (fun _ _ h => h), fun h => h ▸ .refl⟩

/-- Any function invariant under every `r`-step is invariant under `ReflTransGen r`. -/
theorem preserves (f : α → β) (hinv : ∀ x y, r x y → f x = f y)
    (h : ReflTransGen r a b) : f a = f b :=
  of_refl_trans (q := fun x y => f x = f y) (fun _ => rfl) Eq.trans hinv h

/-- Equivalence characterizing invariance of `f` under `ReflTransGen r`. -/
theorem preserves_iff (f : α → β) :
    (∀ x y, ReflTransGen r x y → f x = f y) ↔ (∀ x y, r x y → f x = f y) :=
  ⟨fun h x y hxy => h x y (single hxy), fun hinv _ _ h => preserves f hinv h⟩

end ReflTransGen

end Optic

end
