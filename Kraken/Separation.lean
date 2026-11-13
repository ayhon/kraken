module

public import Std.Data.ExtHashMap

/-!
# Separation Logic over `ExtHashMap`

Defines the separating conjunction `p ⋆ q` and empty-map predicate `emp` over `Std.ExtHashMap`,
together with disjoint-union properties, commutativity, associativity, identity, and extraction
lemmas used by `ecancel`.
-/

public section

namespace Std.ExtHashMap

variable {key value : Type} [BEq key] [EquivBEq key] [Hashable key] [LawfulHashable key] [LawfulBEq key]

/-! ### Separating conjunction and empty map -/

def sep (p q : ExtHashMap key value → Prop) (m : ExtHashMap key value) : Prop :=
  ∃ a b, a.union b = m ∧ a.inter b = ∅ ∧ p a ∧ q b

-- Type with: \st
infixl:60 " ⋆ " => sep
notation:70 m " =⋆ " P => P m

def emp : ExtHashMap key value → Prop := fun m => m = ∅

/-! ### Disjoint union and intersection lemmas -/

omit [LawfulBEq key] in
theorem disjoint_symm {m1 m2 : ExtHashMap key value} (h : m1.inter m2 = ∅) :
    m2.inter m1 = ∅ := by
  simpa only [eq_empty_iff_forall_not_mem, inter_eq, mem_inter_iff, and_comm] using h

omit [LawfulBEq key] in
private theorem disjoint_symm_iff {m1 m2 : ExtHashMap key value} :
    (m1.inter m2 = ∅) = (m2.inter m1 = ∅) :=
  propext ⟨disjoint_symm, disjoint_symm⟩

theorem union_comm_of_disjoint (m1 m2 : ExtHashMap key value) (h_disj : m1.inter m2 = ∅) :
    m1.union m2 = m2.union m1 := by
  apply ExtHashMap.ext_getElem?
  intro k
  simp only [union_eq]
  rw [getElem?_union, getElem?_union]
  have hd := eq_empty_iff_forall_not_mem.mp h_disj k
  simp only [inter_eq, mem_inter_iff] at hd
  cases h1 : m1[k]? <;> cases h2 : m2[k]? <;> simp <;>
    simp_all [mem_iff_isSome_getElem?]

theorem get_union_l_disjoint (m1 m2 : ExtHashMap key value) (k : key) (v : value)
    (h_disj : m1.inter m2 = ∅) (h : m1.get? k = some v) :
    (m1.union m2).get? k = some v := by
  rw [get?_eq_getElem?] at h
  rw [get?_eq_getElem?, union_comm_of_disjoint m1 m2 h_disj]
  simp only [union_eq, getElem?_union, h, Option.some_or]

theorem union_union_override (m1 m2 m3 : ExtHashMap key value) (h_sub : ∀ k, k ∈ m1 → k ∈ m3) :
    (m1.union m2).union m3 = m2.union m3 := by
  apply ExtHashMap.ext_getElem?
  intro k
  simp only [union_eq]
  rw [getElem?_union, getElem?_union, getElem?_union]
  cases h3 : m3[k]?
  · have h_not_mem3 : ¬ k ∈ m3 := by
      intro h_mem
      have h_some := getElem?_eq_some_getElem h_mem
      rw [h3] at h_some
      contradiction
    have h_not_mem1 : ¬ k ∈ m1 := fun h => h_not_mem3 (h_sub k h)
    rw [getElem?_eq_none h_not_mem1]
    cases m2[k]? <;> rfl
  · rfl

private theorem union_assoc (m1 m2 m3 : ExtHashMap key value) :
    (m1.union m2).union m3 = m1.union (m2.union m3) := by
  apply ExtHashMap.ext_getElem?
  intro k
  simpa only [union_eq, getElem?_union] using (Option.or_assoc).symm

omit [LawfulBEq key] in
private theorem disjoint_union_l (a b c : ExtHashMap key value) :
    ((a.union b).inter c = ∅) = (a.inter c = ∅ ∧ b.inter c = ∅) := by
  apply propext
  simp only [eq_empty_iff_forall_not_mem, inter_eq, mem_inter_iff, union_eq, mem_union_iff]
  grind

omit [LawfulBEq key] in
private theorem disjoint_union_r (a b c : ExtHashMap key value) :
    (a.inter (b.union c) = ∅) = (a.inter b = ∅ ∧ a.inter c = ∅) := by
  rw [disjoint_symm_iff, disjoint_union_l, disjoint_symm_iff (m1 := b), disjoint_symm_iff (m1 := c)]

/-! ### Algebraic laws and extraction lemmas for `sep` -/

theorem sep_comm (p q : ExtHashMap key value → Prop) : p ⋆ q = q ⋆ p := by
  have h (p q : ExtHashMap key value → Prop) (m) (h : (p ⋆ q) m) : (q ⋆ p) m := by
    have ⟨a, b, h_union, h_inter, hp, hq⟩ := h
    refine ⟨b, a, by rw [← h_union, union_comm_of_disjoint a b h_inter], disjoint_symm h_inter, hq, hp⟩
  funext m
  exact propext ⟨h p q m, h q p m⟩

theorem sep_assoc (p q r : ExtHashMap key value → Prop) : p ⋆ q ⋆ r = p ⋆ (q ⋆ r) := by
  funext m
  apply propext
  constructor
  · intro h
    have ⟨ab, c, habc_union, habc_inter, ⟨a, b, hab_union, hab_inter, hp, hq⟩, hr⟩ := h
    subst hab_union
    refine ⟨a, b.union c, (union_assoc a b c).symm.trans habc_union, ?_, hp, ⟨b, c, rfl, ?_, hq, hr⟩⟩
    · have ⟨hac, hbc⟩ := (disjoint_union_l a b c).mp habc_inter
      exact (disjoint_union_r a b c).mpr ⟨hab_inter, hac⟩
    · exact ((disjoint_union_l a b c).mp habc_inter).2
  · intro h
    have ⟨a, bc, habc_union, habc_inter, hp, ⟨b, c, hbc_union, hbc_inter, hq, hr⟩⟩ := h
    subst hbc_union
    refine ⟨a.union b, c, (union_assoc a b c).trans habc_union, ?_, ⟨a, b, rfl, ?_, hp, hq⟩, hr⟩
    · have ⟨hab, hac⟩ := (disjoint_union_r a b c).mp habc_inter
      exact (disjoint_union_l a b c).mpr ⟨hac, hbc_inter⟩
    · exact ((disjoint_union_r a b c).mp habc_inter).1

theorem sep_comm_l (p q r : ExtHashMap key value → Prop) : p ⋆ (q ⋆ r) = q ⋆ (p ⋆ r) := by
  rw [← sep_assoc, sep_comm p q, sep_assoc]

theorem emp_sep (p : ExtHashMap key value → Prop) : emp ⋆ p = p := by
  funext m
  apply propext
  constructor
  · rintro ⟨a, b, h_union, _h_inter, ha, hb⟩
    rw [ha] at h_union
    have : b = m := by
      apply ExtHashMap.ext_getElem?
      intro k
      simpa only [union_eq, getElem?_union_of_not_mem_left not_mem_empty] using
        congrArg (fun x => x[k]?) h_union
    simpa only [this] using hb
  · intro hp
    refine ⟨∅, m, ?_, ?_, rfl, hp⟩
    · apply ExtHashMap.ext_getElem?
      intro k
      simp only [union_eq, getElem?_union_of_not_mem_left not_mem_empty]
    · apply eq_empty_iff_forall_not_mem.mpr
      intro k hk
      exact not_mem_empty (mem_inter_iff.mp hk).1

theorem sep_emp (p : ExtHashMap key value → Prop) : p ⋆ emp = p := by
  rw [sep_comm, emp_sep]

theorem sep_extract_here {p a : ExtHashMap key value → Prop} (h : p = a) : p = a ⋆ emp := by
  rw [h, sep_emp]

omit [LawfulBEq key] in
theorem sep_extract_head {p a : ExtHashMap key value → Prop} (q : ExtHashMap key value → Prop)
    (h : p = a) : p ⋆ q = a ⋆ q := by
  rw [h]

theorem sep_extract_tail (p : ExtHashMap key value → Prop) {q a : ExtHashMap key value → Prop}
    (h : q = a) : p ⋆ q = a ⋆ p := by
  rw [h, sep_comm]

theorem sep_extract_left {p a p' : ExtHashMap key value → Prop} (q : ExtHashMap key value → Prop)
    (h : p = a ⋆ p') : p ⋆ q = a ⋆ (p' ⋆ q) := by
  rw [h, sep_assoc]

theorem sep_extract_right (p : ExtHashMap key value → Prop) {q a q' : ExtHashMap key value → Prop}
    (h : q = a ⋆ q') : p ⋆ q = a ⋆ (p ⋆ q') := by
  rw [h, sep_comm_l]

instance : Std.Commutative (sep : (ExtHashMap key value → Prop) → _) := ⟨sep_comm⟩
instance : Std.Associative (sep : (ExtHashMap key value → Prop) → _) := ⟨sep_assoc⟩
instance : Std.LawfulIdentity (sep : (ExtHashMap key value → Prop) → _) emp where
  left_id := emp_sep
  right_id := sep_emp

end Std.ExtHashMap

end
