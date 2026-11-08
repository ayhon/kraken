module

public import Lean.ToExpr

@[expose] public section

/-
Common Kraken executable layout.
-/

namespace Kraken


abbrev Label := String
instance : Repr ByteArray where reprPrec _ _ := "<opaque byte array>"

deriving instance Lean.ToExpr for ByteArray

inductive Directive (Instr : Type)
  | instr (_ : Instr)
  | label (_ : Label)
  | byteArray (_ : ByteArray)
  deriving BEq, DecidableEq, Repr, Hashable, Lean.ToExpr

structure Sized Directive where
  directive : Directive
  size : Nat

abbrev Program Instr := List (Directive Instr)

structure Executable (Instr : Type) where
  startAddr : Int64
  program : List (Sized (Directive Instr))

-- JP: why is `size` not `Directive → Nat`?
class Layout {Instr : Type} (p : Program Instr) where
  start : Int64
  size : Nat → Nat

variable {Instr : Type}

def Program.size (p : Program Instr) [layout : Layout p] := p.mapIdx (fun idx _ => Layout.size p idx) |>.sum

def Program.labels (p : Program Instr) : List Label := p.filterMap fun
  | .label l => l
  | _ => none

-- NOTE: Maybe this should not be a property on `Layout`, but on `Program`...
class Layout.IsWellFormed (p : Program Instr) [Layout p] where
  no_overflow : p.size < 2^64
  unique_labels : p.labels.Nodup

class abbrev WellFormedLayout (p : Program Instr) := Layout p, Layout.IsWellFormed p

def Layout.apply (prog : Program Instr) (l : Layout prog) : Executable Instr :=
  {startAddr := l.start, program := prog.mapIdx (fun i directive => {directive, size := l.size i})}

abbrev Program.toExecutable (prog : Program Instr) [l : Layout prog] := l.apply prog

abbrev _root_.List.toExecutable (prog : Program Instr) [l : Layout prog] := l.apply prog

@[instance_reducible]
def Layout.drop (p₁ : Program Instr) {p₂} [l : Layout (p₁ ++ p₂)] : Layout p₂ where
  start := l.start + .ofNat (p₁.mapIdx (fun i _ => l.size i) |>.sum)
  size i := l.size (i + p₁.length)

@[instance_reducible]
def Layout.take (p₁ : Program Instr) {p₂} [l : Layout (p₁ ++ p₂)] : Layout p₁ where
  start := l.start
  size i := l.size i

theorem Program.size_append (p₁ p₂ : Program Instr) [layout : Layout (p₁ ++ p₂)] :
    letI := layout.take p₁
    letI := layout.drop p₁
    (p₁ ++ p₂).size = p₁.size + p₂.size
    := by
  simp only [size, Layout.size]
  grind

@[instance_reducible]
nonrec def WellFormedLayout.drop (p₁ : Program Instr) {p₂} [l : WellFormedLayout (p₁ ++ p₂)] :
    WellFormedLayout p₂ := {l.drop p₁ with
    no_overflow := Nat.lt_of_add_left_lt <| Program.size_append (layout := l.toLayout) ▸ l.no_overflow
    unique_labels := by grind [Program.labels, l.unique_labels]
  }

@[instance_reducible]
nonrec def WellFormedLayout.take (p₁ : Program Instr) {p₂} [l : WellFormedLayout (p₁ ++ p₂)] :
    WellFormedLayout p₁ := {l.take p₁ with
    no_overflow := Nat.lt_of_add_right_lt <| Program.size_append (layout := l.toLayout) ▸ l.no_overflow
    unique_labels := by grind [Program.labels, l.unique_labels]
  }

structure Addressable (Directive : Type) extends Sized Directive where (addr : Int64)

-- Returns each directive paired with its start address and size.
-- TODO: tail-recursive version for efficiency?
def Executable.withAddresses {Instr : Type} (e : Executable Instr) : List (Addressable (Directive Instr)) :=
  let {startAddr, program} := e
  match program with
  | [] => []
  | instr :: program =>
    {instr with addr := startAddr} :: Executable.withAddresses {startAddr := startAddr + .ofNat instr.size, program}
termination_by e.2

def Executable.directivesAtAddress {Instr : Type} (e : Executable Instr) (a : Int64) : List (Sized (Directive Instr)) :=
  let starts_at_a := e.withAddresses.dropWhile (·.addr ≠ a)
  (starts_at_a.takeWhile (·.addr = a)).map (·.toSized)

def Executable.directivesFromAddress {Instr : Type} (e : Executable Instr) (a : Int64) : List (Sized (Directive Instr)) :=
  let starts_at_a := e.withAddresses.dropWhile (·.addr ≠ a)
  starts_at_a.map (·.toSized)

theorem Executable.withAddresses_map_snd {Instr : Type} (program : List (Sized (Directive Instr))) (startAddr : Int64) :
    (Executable.withAddresses {startAddr, program}).map (·.toSized) = program := by
  induction program generalizing startAddr <;> grind [Executable.withAddresses]

theorem Executable.withAddresses_dropWhile_start {Instr : Type} (program : List (Sized (Directive Instr))) (startAddr : Int64) :
    (Executable.withAddresses {startAddr, program}).dropWhile (fun x => x.addr ≠ startAddr) =
      Executable.withAddresses {startAddr, program} := by
  cases program <;> grind [Executable.withAddresses, List.dropWhile_cons, List.dropWhile_nil]

theorem Executable.directivesFromStart {Instr : Type} (prog : Program Instr) [layout : Layout prog] :
    prog.toExecutable.directivesFromAddress layout.start =
      prog.mapIdx (fun i directive => {directive, size := layout.size i}) := by
  grind [Executable.withAddresses_dropWhile_start, Executable.withAddresses_map_snd, Executable.directivesFromAddress, Layout.apply]

theorem directivesAtFromPrefix {Instr : Type} (e: Executable Instr) (a: Int64):
  let starts_at_a := e.withAddresses.dropWhile (·.addr ≠ a)
  e.directivesFromAddress a = e.directivesAtAddress a ++ (starts_at_a.dropWhile (·.addr = a)).map (·.toSized) := by
  dsimp [Executable.directivesFromAddress, Executable.directivesAtAddress]
  rw [← List.map_append]
  rw [List.takeWhile_append_dropWhile]

theorem Program.map_size_toExecutable_eq (p : Program Instr) [Layout p] :
    (p.toExecutable.program.map (·.size)).sum = p.size := by
  dsimp [Program.toExecutable, Layout.apply, Program.size]
  congr 1
  generalize (Layout.size p) = sz
  induction p generalizing sz <;> simp [List.mapIdx_cons, *]

@[grind hom] theorem Int64.toBitVec_ofNat_grind (a : Nat) :
    (Int64.ofNat a).toBitVec = OfNat.ofNat a := by
  rw [Int64.toBitVec_ofNat']; rfl

private theorem add_ofNat_ne_self (a : Int64) {n : Nat} (hpos : 0 < n) (hlt : n < UInt64.size) :
    a + .ofNat n ≠ a := by
  grind

private theorem add_ofNat_add (a : Int64) (m n : Nat) :
    a + .ofNat m + .ofNat n = a + .ofNat (m + n) := by
  grind

private theorem withAddresses_dropWhile_WellFormed {Instr : Type}
    (program : List (Sized (Directive Instr))) (startAddr a : Int64)
    (hwf : (program.map (·.size)).sum < UInt64.size)
    {y : Addressable (Directive Instr)} {ys : List (Addressable (Directive Instr))}
    (h : ((Executable.withAddresses {startAddr, program}).dropWhile (·.addr ≠ a)).dropWhile (·.addr = a) = y :: ys) :
    (Executable.withAddresses {startAddr, program}).dropWhile (·.addr ≠ y.addr) = y :: ys ∧
    (Executable.directivesAtAddress {startAddr, program} a).foldl (fun p d => p + .ofNat d.size) a = y.addr ∧
    0 < (((Executable.withAddresses {startAddr, program}).dropWhile (·.addr ≠ a)).takeWhile (·.addr = a)).length ∧
    ∃ offset, 0 < offset ∧ offset ≤ (program.map (·.size)).sum ∧ y.addr = startAddr + .ofNat offset := by
  induction program generalizing startAddr with
  | nil =>
    rw [Executable.withAddresses] at h
    contradiction
  | cons c rest ih =>
    simp only [List.map_cons, List.sum_cons] at hwf ⊢
    by_cases ha : startAddr = a
    · subst ha
      have hpos_take : 0 < (((Executable.withAddresses {startAddr, program := c :: rest}).dropWhile (·.addr ≠ startAddr)).takeWhile (·.addr = startAddr)).length := by
        rw [Executable.withAddresses_dropWhile_start, Executable.withAddresses]
        simp
      rw [Executable.withAddresses_dropWhile_start, Executable.withAddresses] at h
      simp only [List.dropWhile_cons, decide_true, ↓reduceIte] at h
      by_cases hc : c.size = 0
      · have ha0 : startAddr + .ofNat c.size = startAddr := by simp [hc]
        rw [ha0, ← Executable.withAddresses_dropWhile_start rest startAddr] at h
        obtain ⟨hdrop, hfold, _, offset, hpos, hle, hy⟩ := ih startAddr (by omega) h
        have hne : startAddr ≠ y.addr := by
          rw [hy]; exact Ne.symm (add_ofNat_ne_self startAddr hpos (by omega))
        refine ⟨?_, ?_, hpos_take, offset, hpos, by omega, hy⟩
        · rw [Executable.withAddresses]
          simp only [List.dropWhile_cons, ne_eq, hne, not_false_eq_true, decide_true, ↓reduceIte, ha0]
          exact hdrop
        · dsimp [Executable.directivesAtAddress] at hfold ⊢
          rw [Executable.withAddresses_dropWhile_start, Executable.withAddresses]
          simp only [List.takeWhile_cons, decide_true, ↓reduceIte, List.map_cons, List.foldl_cons, ha0]
          rw [← Executable.withAddresses_dropWhile_start rest startAddr]
          exact hfold
      · have hpos : 0 < c.size := Nat.pos_of_ne_zero hc
        have hne : startAddr + .ofNat c.size ≠ startAddr := add_ofNat_ne_self startAddr hpos (by omega)
        cases rest with
        | nil => rw [Executable.withAddresses] at h; contradiction
        | cons d rest' =>
          rw [Executable.withAddresses] at h
          simp only [List.dropWhile_cons, hne, decide_false, Bool.false_eq_true, ↓reduceIte] at h
          injection h with hy hys
          have hy_addr : y.addr = startAddr + .ofNat c.size := by rw [← hy]
          refine ⟨?_, ?_, hpos_take, c.size, hpos, by omega, hy_addr⟩
          · rw [Executable.withAddresses]
            simp only [List.dropWhile_cons, ne_eq, hy_addr, hne.symm, not_false_eq_true, decide_true, ↓reduceIte]
            rw [Executable.withAddresses_dropWhile_start, Executable.withAddresses, hy, hys]
          · dsimp [Executable.directivesAtAddress]
            rw [Executable.withAddresses_dropWhile_start, Executable.withAddresses]
            simp only [List.takeWhile_cons, decide_true, ↓reduceIte]
            rw [Executable.withAddresses]
            simp [hne, hy_addr]
    · rw [Executable.withAddresses] at h
      simp only [List.dropWhile_cons, ne_eq, ha, not_false_eq_true, decide_true, ↓reduceIte] at h
      obtain ⟨hdrop, hfold, hpos_take, offset', hpos', hle', hy⟩ := ih (startAddr + .ofNat c.size) (by omega) h
      rw [add_ofNat_add] at hy
      have hne : startAddr ≠ y.addr := by
        rw [hy]; exact Ne.symm (add_ofNat_ne_self startAddr (by omega) (by omega))
      refine ⟨?_, ?_, ?_, c.size + offset', by omega, by omega, hy⟩
      · rw [Executable.withAddresses]
        simp only [List.dropWhile_cons, ne_eq, hne, not_false_eq_true, decide_true, ↓reduceIte]
        exact hdrop
      · dsimp [Executable.directivesAtAddress] at hfold ⊢
        rw [Executable.withAddresses]
        simp only [List.dropWhile_cons, ha, not_false_eq_true, decide_true, ↓reduceIte]
        exact hfold
      · rw [Executable.withAddresses]
        simp only [List.dropWhile_cons, ne_eq, ha, not_false_eq_true, decide_true, ↓reduceIte]
        exact hpos_take

theorem Executable.directivesFromAddress_split {Instr : Type}
    (prog : Program Instr) [WellFormedLayout prog] (pc : Int64) :
    let e := prog.toExecutable
    let at_pc := e.directivesAtAddress pc
    let pc' := at_pc.foldl (fun p d => p + .ofNat d.size) pc
    e.directivesFromAddress pc = at_pc ∨
    (e.directivesFromAddress pc = at_pc ++ e.directivesFromAddress pc' ∧
     (e.withAddresses.dropWhile (·.addr ≠ pc')).length <
       (e.withAddresses.dropWhile (·.addr ≠ pc)).length) := by
  have hwf : (prog.toExecutable.program.map (·.size)).sum < UInt64.size := by
    rw [Program.map_size_toExecutable_eq]
    exact Layout.IsWellFormed.no_overflow
  rcases h_e : prog.toExecutable with ⟨startAddr, program⟩
  rw [h_e] at hwf
  dsimp only
  have h_prefix := directivesAtFromPrefix {startAddr, program} pc
  dsimp only at h_prefix
  generalize h_drop : ((Executable.withAddresses {startAddr, program}).dropWhile (·.addr ≠ pc)).dropWhile (·.addr = pc) = after_pc at h_prefix
  cases after_pc with
  | nil =>
    left
    simpa using h_prefix
  | cons y ys =>
    right
    obtain ⟨h_next_from, h_fold, h_take_pos, _⟩ := withAddresses_dropWhile_WellFormed program startAddr pc hwf h_drop
    rw [h_fold]
    refine ⟨?_, ?_⟩
    · rw [h_prefix]
      dsimp [Executable.directivesFromAddress]
      rw [h_next_from]
    · rw [h_next_from]
      have h_split := List.takeWhile_append_dropWhile (p := (·.addr = pc))
        (l := (Executable.withAddresses {startAddr, program}).dropWhile (·.addr ≠ pc))
      have h_len_eq := congrArg List.length h_split
      rw [List.length_append, h_drop] at h_len_eq
      omega

theorem Executable.mem_of_mem_directivesAtAddress {Instr : Type} {e : Executable Instr}
    {a : Int64} {c : Sized (Directive Instr)} (h : c ∈ e.directivesAtAddress a) : c ∈ e.program := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  rw [← Executable.withAddresses_map_snd e.program e.startAddr]
  exact List.mem_map_of_mem
    ((List.dropWhile_sublist _).subset ((List.takeWhile_sublist _).subset hx))

/-- The sum of sizes of the first `n` directives of `e`. -/
def Executable.sizeBefore {Instr : Type} (e : Executable Instr) (n : Nat) : Nat :=
  ((e.program.take n).map (·.size)).sum

/--
The address of the `n`-th directive of `e`: the start address of `e` plus the sum of sizes of the
first `n` directives.
-/
def Executable.addrOf {Instr : Type} (e : Executable Instr) (n : Nat) : Int64 :=
  e.startAddr + .ofNat (e.sizeBefore n)

@[simp] theorem Executable.addrOf_zero {Instr : Type} (e : Executable Instr) : e.addrOf 0 = e.startAddr := by
  grind [sizeBefore, addrOf]

@[grind →] theorem Executable.sizeBefore_succ {Instr : Type} (e : Executable Instr) {n : Nat}
    {c : Sized (Directive Instr)} (hc : e.program[n]? = some c) : e.sizeBefore (n + 1) = e.sizeBefore n + c.size := by
  simp [sizeBefore, List.take_add_one, hc]

theorem Executable.sizeBefore_add {Instr : Type} (e : Executable Instr) (j i : Nat) :
    e.sizeBefore (j + i) = e.sizeBefore j + (((e.program.drop j).take i).map (·.size)).sum := by
  simp [sizeBefore, List.take_add]

theorem Executable.sizeBefore_mono {Instr : Type} (e : Executable Instr) {j k : Nat}
    (h : j ≤ k) : e.sizeBefore j ≤ e.sizeBefore k := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
  simp [sizeBefore_add]

theorem Executable.addrOf_succ {Instr : Type} (e : Executable Instr) {n : Nat} {c : Sized (Directive Instr)}
    (hc : e.program[n]? = some c) : e.addrOf (n + 1) = e.addrOf n + .ofNat c.size := by
  grind [addrOf]

theorem Executable.sizeBefore_le {Instr : Type} (e : Executable Instr) (n : Nat) :
    e.sizeBefore n ≤ (e.program.map (·.size)).sum := by
  simpa [sizeBefore, List.take_of_length_le (Nat.le_max_right n e.program.length)] using
    e.sizeBefore_mono (Nat.le_max_left n e.program.length)

theorem Program.sizeBefore_lt {Instr : Type} (prog : Program Instr) [WellFormedLayout prog] (n : Nat) :
    prog.toExecutable.sizeBefore n < 2^64 :=
  Nat.lt_of_le_of_lt (prog.toExecutable.sizeBefore_le n)
    (Program.map_size_toExecutable_eq prog ▸ Layout.IsWellFormed.no_overflow)

theorem Program.sizeBefore_eq_of_addrOf_eq {Instr : Type} (prog : Program Instr) [WellFormedLayout prog]
    {j k : Nat} (h : prog.toExecutable.addrOf j = prog.toExecutable.addrOf k) :
    prog.toExecutable.sizeBefore j = prog.toExecutable.sizeBefore k := by
  have hj := Program.sizeBefore_lt prog j
  have hk := Program.sizeBefore_lt prog k
  grind [Executable.addrOf]

theorem Executable.getElem?_withAddresses_mk {Instr : Type} :
    ∀ (program : List (Sized (Directive Instr))) (startAddr : Int64) (k : Nat),
      (Executable.withAddresses {startAddr, program})[k]?
        = program[k]?.map (fun c => {c with addr := Executable.addrOf {startAddr, program} k})
  | [], a, k => by rw [Executable.withAddresses]; simp
  | c :: program, a, 0 => by
    rw [Executable.withAddresses]
    simp
  | c :: program, a, k + 1 => by
    rw [Executable.withAddresses]
    simp only [List.getElem?_cons_succ, getElem?_withAddresses_mk program _ k]
    congr 2
    funext c'
    simp only [addrOf, sizeBefore, List.take_succ_cons, List.map_cons, List.sum_cons]
    grind

theorem Executable.getElem?_withAddresses_eq {Instr : Type} (e : Executable Instr) (k : Nat) :
    e.withAddresses[k]? = e.program[k]?.map (fun c => {c with addr := e.addrOf k}) :=
  getElem?_withAddresses_mk e.program e.startAddr k


private theorem dropWhile_eq_drop_of {α : Type _} {p : α → Bool} {l : List α} {j : Nat}
    (hprior : ∀ k, k < j → ∀ c, l[k]? = some c → p c = true)
    (hhead : ∀ c, l[j]? = some c → p c = false) :
    l.dropWhile p = l.drop j := by
  rw [List.dropWhile_eq_drop_findIdx_not]
  by_cases hj : j < l.length
  · rw [(List.findIdx_eq hj).mpr ⟨by simp [hhead _ (List.getElem?_eq_getElem hj)],
      fun k hk => by simp [hprior k hk _ (List.getElem?_eq_getElem (by omega))]⟩]
  · rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hj), List.drop_eq_nil_iff]
    refine Nat.le_of_eq (List.findIdx_eq_length.mpr fun x hx => ?_).symm
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    simp [hprior i (by omega) _ (List.getElem?_eq_getElem hi)]

theorem Executable.withAddresses_dropWhile_addrOf {Instr : Type} (e : Executable Instr) (j n : Nat)
    (hj : e.addrOf j = e.addrOf n)
    (hfresh : ∀ k, k < j → e.addrOf k ≠ e.addrOf n) :
    e.withAddresses.dropWhile (·.addr ≠ e.addrOf n)
      = e.withAddresses.drop j := by
  apply dropWhile_eq_drop_of
  · intro k hk c hc
    rw [Executable.getElem?_withAddresses_eq] at hc
    obtain ⟨dz, -, rfl⟩ := Option.map_eq_some_iff.mp hc
    simpa using hfresh k hk
  · intro c hc
    rw [Executable.getElem?_withAddresses_eq] at hc
    obtain ⟨dz, -, rfl⟩ := Option.map_eq_some_iff.mp hc
    simpa using hj

private theorem add_ofNat_inj {a : Int64} {m n : Nat} (hm : m < UInt64.size) (hn : n < UInt64.size)
    (h : a + .ofNat m = a + .ofNat n) : m = n := by
  grind

private theorem dropWhile_append_of_ne_nil {α : Type _} {p : α → Bool} {l₁ l₂ : List α}
    (h : l₁.dropWhile p ≠ []) :
    (l₁ ++ l₂).dropWhile p = l₁.dropWhile p ++ l₂ := by
  induction l₁ with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.cons_append, List.dropWhile_cons] at h ⊢
    split at h <;> simp_all

private theorem dropWhile_append_of_eq_nil {α : Type _} {p : α → Bool} {l₁ l₂ : List α}
    (h : l₁.dropWhile p = []) :
    (l₁ ++ l₂).dropWhile p = l₂.dropWhile p := by
  induction l₁ with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, List.dropWhile_cons] at h ⊢
    split at h <;> simp_all

private theorem takeWhile_append_of_none {α : Type _} {p : α → Bool} {l₁ l₂ : List α}
    (h : ∀ y ∈ l₂, p y = false) :
    (l₁ ++ l₂).takeWhile p = l₁.takeWhile p := by
  induction l₁ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons y _ => simp [h y List.mem_cons_self]
  | cons _ _ ih =>
    simp only [List.cons_append, List.takeWhile_cons]
    split <;> simp [ih]

private theorem takeWhile_append_of_all {α : Type _} {p : α → Bool} {l₁ l₂ : List α}
    (h : ∀ x ∈ l₁, p x = true) :
    (l₁ ++ l₂).takeWhile p = l₁ ++ l₂.takeWhile p := by
  induction l₁ with
  | nil => rfl
  | cons x _ ih =>
    simp [h x List.mem_cons_self, ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

private theorem mem_takeWhile_prop {α : Type _} {p : α → Bool} {l : List α} {x : α}
    (hx : x ∈ l.takeWhile p) : p x = true := by
  induction l with
  | nil => contradiction
  | cons _ _ ih =>
    simp only [List.takeWhile_cons] at hx
    split at hx
    · rename_i hy
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hy
      · exact ih hx
    · contradiction

private theorem size_zero_of_sum_zero {Instr : Type}
    {cs : List (Sized (Directive Instr))}
    (h0 : (cs.map (·.size)).sum = 0) {c : Sized (Directive Instr)} (hc : c ∈ cs) :
    c.size = 0 := by
  induction cs with
  | nil => contradiction
  | cons _ _ ih =>
    simp only [List.map_cons, List.sum_cons, Nat.add_eq_zero_iff] at h0
    rcases List.mem_cons.mp hc with rfl | hc
    · exact h0.1
    · exact ih h0.2 hc

private theorem withAddresses_append {Instr : Type}
    (prog₁ prog₂ : List (Sized (Directive Instr))) (startAddr : Int64) :
    Executable.withAddresses {startAddr, program := prog₁ ++ prog₂} =
      Executable.withAddresses {startAddr, program := prog₁} ++
        Executable.withAddresses
          {startAddr := startAddr + .ofNat ((prog₁.map (·.size)).sum), program := prog₂} := by
  induction prog₁ generalizing startAddr with
  | nil => simp [Executable.withAddresses]
  | cons _ _ ih =>
    rw [List.cons_append, Executable.withAddresses, Executable.withAddresses]
    simp [ih, add_ofNat_add]

private theorem mem_withAddresses_offset {Instr : Type}
    (e : Executable Instr)
    {x : Addressable (Directive Instr)}
    (hx : x ∈ e.withAddresses) :
    ∃ off, off + x.size ≤ (e.program.map (·.size)).sum ∧ x.addr = e.startAddr + .ofNat off := by
  rcases e with ⟨startAddr, prog⟩
  induction prog generalizing startAddr with
  | nil => rw [Executable.withAddresses] at hx; contradiction
  | cons c _ ih =>
    rw [Executable.withAddresses] at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨0, by simp, by simp⟩
    · obtain ⟨off, hle, haddr⟩ := ih (startAddr + .ofNat c.size) hx
      exact ⟨c.size + off, by simp at hle ⊢; omega, by simpa [add_ofNat_add] using haddr⟩

private theorem dropWhile_withAddresses_ne_nil {Instr : Type}
    (e : Executable Instr) (pc : Int64)
    (h : e.withAddresses.dropWhile (·.addr ≠ pc) ≠ []) :
    ∃ off cs, (∀ c ∈ cs, c ∈ e.program) ∧
      off + (cs.map (·.size)).sum = (e.program.map (·.size)).sum ∧
      pc = e.startAddr + .ofNat off ∧
      e.withAddresses.dropWhile (·.addr ≠ pc) =
        Executable.withAddresses {startAddr := pc, program := cs} := by
  rcases e with ⟨startAddr, prog⟩
  induction prog generalizing startAddr with
  | nil => rw [Executable.withAddresses] at h; simp at h
  | cons d ds ih =>
    by_cases ha : startAddr = pc
    · subst ha
      exact ⟨0, d :: ds, fun _ hc => hc, by simp, by simp,
        Executable.withAddresses_dropWhile_start (d :: ds) startAddr⟩
    · rw [Executable.withAddresses] at h ⊢
      simp only [List.dropWhile_cons, ne_eq, ha, not_false_eq_true, decide_true, ↓reduceIte] at h ⊢
      obtain ⟨off, cs, hsub, hsum, hpc, heq⟩ := ih (startAddr + .ofNat d.size) h
      exact ⟨d.size + off, cs, fun c hc => List.mem_cons_of_mem _ (hsub c hc),
        by simp at hsum ⊢; omega, by simpa [add_ofNat_add] using hpc, heq⟩

private theorem withAddresses_all_addr_eq_of_sum_zero {Instr : Type}
    (cs : List (Sized (Directive Instr))) (pc : Int64)
    (h0 : (cs.map (·.size)).sum = 0) :
    ∀ x ∈ Executable.withAddresses {startAddr := pc, program := cs}, x.addr = pc := by
  induction cs with
  | nil => intro x hx; rw [Executable.withAddresses] at hx; contradiction
  | cons c _ ih =>
    simp only [List.map_cons, List.sum_cons, Nat.add_eq_zero_iff] at h0
    intro x hx
    rw [Executable.withAddresses] at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · rfl
    · have hpc0 : pc + .ofNat c.size = pc := by simp [h0.1]
      rw [hpc0] at hx
      exact ih h0.2 x hx

theorem Program.toExecutable_append_program {Instr : Type} (p₁ p₂ : Program Instr)
    [l : Layout (p₁ ++ p₂)] :
    letI := l.take p₁
    letI := l.drop p₁
    (p₁ ++ p₂).toExecutable.program = p₁.toExecutable.program ++ p₂.toExecutable.program := by
  simp only [Layout.apply, Layout.size, List.mapIdx_append]

theorem Program.toExecutable_append_withAddresses {Instr : Type} (p₁ p₂ : Program Instr)
    [l : Layout (p₁ ++ p₂)] :
    letI := l.take p₁
    letI := l.drop p₁
    (p₁ ++ p₂).toExecutable.withAddresses =
      p₁.toExecutable.withAddresses ++ p₂.toExecutable.withAddresses := by
  let e₁ := (letI := l.take p₁; p₁.toExecutable)
  let e₂ := (letI := l.drop p₁; p₂.toExecutable)
  have hprog : (p₁ ++ p₂).toExecutable.program = e₁.program ++ e₂.program :=
    toExecutable_append_program p₁ p₂
  have hstart₁ : (p₁ ++ p₂).toExecutable.startAddr = e₁.startAddr := rfl
  have hstart₂ : e₁.startAddr + .ofNat ((e₁.program.map (·.size)).sum) = e₂.startAddr := by
    letI := l.take p₁
    rw [Program.map_size_toExecutable_eq p₁]
    rfl
  rcases h_e : (p₁ ++ p₂).toExecutable with ⟨sa, prog⟩
  rw [h_e] at hprog hstart₁
  subst hprog hstart₁
  rw [withAddresses_append, hstart₂]

theorem Program.mem_labels_of_mem_withAddresses {Instr : Type} (p : Program Instr) [Layout p]
    {x : Addressable (Directive Instr)} {l : Label}
    (hx : x ∈ p.toExecutable.withAddresses) (hd : x.directive = .label l) :
    l ∈ Program.labels p := by
  have hsz : x.toSized ∈ p.toExecutable.program := by
    rw [← Executable.withAddresses_map_snd p.toExecutable.program p.toExecutable.startAddr]
    exact List.mem_map_of_mem hx
  simp only [Layout.apply, List.mem_iff_getElem] at hsz
  obtain ⟨i, hi, heq⟩ := hsz
  simp only [List.getElem_mapIdx] at heq
  have hmem : Directive.label l ∈ p := by
    have : p[i]'(by simpa using hi) = .label l := by
      have := congrArg Sized.directive heq
      simpa [hd] using this
    exact this ▸ List.getElem_mem _
  exact List.mem_filterMap.mpr ⟨.label l, hmem, rfl⟩

theorem Executable.directivesAtAddress_take_eq {Instr : Type} (p₁ p₂ : Program Instr)
    [layout : WellFormedLayout (p₁ ++ p₂)] (pc : Int64)
    (hpos : letI := layout.take p₁
            ∃ c ∈ p₁.toExecutable.directivesAtAddress pc, 0 < c.size) :
    letI := layout.take p₁
    (p₁ ++ p₂).toExecutable.directivesAtAddress pc = p₁.toExecutable.directivesAtAddress pc := by
  let e₁ := (letI := layout.toLayout.take p₁; p₁.toExecutable)
  let e₂ := (letI := layout.toLayout.drop p₁; p₂.toExecutable)
  change (p₁ ++ p₂).toExecutable.directivesAtAddress pc = e₁.directivesAtAddress pc
  change ∃ c ∈ e₁.directivesAtAddress pc, 0 < c.size at hpos
  obtain ⟨c, hc, hcsz⟩ := hpos
  dsimp only [Executable.directivesAtAddress] at hc
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
  have hx_drop : x ∈ e₁.withAddresses.dropWhile (·.addr ≠ pc) := (List.takeWhile_sublist _).subset hx
  have hx_mem : x ∈ e₁.withAddresses := (List.dropWhile_sublist _).subset hx_drop
  have hx_addr : x.addr = pc :=
    of_decide_eq_true (mem_takeWhile_prop (p := fun z : Addressable (Directive Instr) => decide (z.addr = pc)) hx)
  have hne_nil : e₁.withAddresses.dropWhile (·.addr ≠ pc) ≠ [] := List.ne_nil_of_mem hx_drop
  have hsum_lt : (e₁.program.map (·.size)).sum + (e₂.program.map (·.size)).sum < UInt64.size := by
    have := layout.no_overflow
    rw [← Program.map_size_toExecutable_eq (p₁ ++ p₂),
        Program.toExecutable_append_program p₁ p₂ (l := layout.toLayout),
        List.map_append, List.sum_append] at this
    exact this
  obtain ⟨off₁, hoff₁, haddr₁⟩ := mem_withAddresses_offset e₁ hx_mem
  have he₂_start : e₂.startAddr = e₁.startAddr + .ofNat ((e₁.program.map (·.size)).sum) := by
    letI := layout.toLayout.take p₁
    rw [Program.map_size_toExecutable_eq p₁]
    rfl
  have hno_e₂ : ∀ y ∈ e₂.withAddresses, (decide (y.addr = pc)) = false := by
    intro y hy
    obtain ⟨off₂, hoff₂, haddr₂⟩ := mem_withAddresses_offset e₂ hy
    rw [he₂_start, add_ofNat_add] at haddr₂
    rw [decide_eq_false_iff_not]
    intro heq
    rw [← hx_addr, haddr₁, haddr₂] at heq
    have := add_ofNat_inj (by omega) (by omega) heq.symm
    omega
  have happ : (p₁ ++ p₂).toExecutable.withAddresses = e₁.withAddresses ++ e₂.withAddresses :=
    Program.toExecutable_append_withAddresses p₁ p₂ (l := layout.toLayout)
  dsimp only [Executable.directivesAtAddress]
  rw [happ, dropWhile_append_of_ne_nil hne_nil, takeWhile_append_of_none hno_e₂]

theorem Executable.directivesAtAddress_drop_eq {Instr : Type} (p₁ p₂ : Program Instr)
    [layout : WellFormedLayout (p₁ ++ p₂)] (pc : Int64)
    (hpos : letI := layout.drop p₁
            ∃ c ∈ p₂.toExecutable.directivesAtAddress pc, 0 < c.size) :
    letI := layout.drop p₁
    ∃ pre, (p₁ ++ p₂).toExecutable.directivesAtAddress pc = pre ++ p₂.toExecutable.directivesAtAddress pc ∧
      ∀ c ∈ pre, c ∈ (p₁ ++ p₂).toExecutable.program ∧ c.size = 0 := by
  let e₁ := (letI := layout.toLayout.take p₁; p₁.toExecutable)
  let e₂ := (letI := layout.toLayout.drop p₁; p₂.toExecutable)
  change ∃ pre, (p₁ ++ p₂).toExecutable.directivesAtAddress pc = pre ++ e₂.directivesAtAddress pc ∧
    ∀ c ∈ pre, c ∈ (p₁ ++ p₂).toExecutable.program ∧ c.size = 0
  change ∃ c ∈ e₂.directivesAtAddress pc, 0 < c.size at hpos
  obtain ⟨c₀, hc₀, _⟩ := hpos
  dsimp only [Executable.directivesAtAddress] at hc₀
  obtain ⟨y₀, hy₀, _⟩ := List.mem_map.mp hc₀
  have hy₀_mem : y₀ ∈ e₂.withAddresses :=
    (List.dropWhile_sublist _).subset ((List.takeWhile_sublist _).subset hy₀)
  have hy₀_addr : y₀.addr = pc :=
    of_decide_eq_true (mem_takeWhile_prop (p := fun z : Addressable (Directive Instr) => decide (z.addr = pc)) hy₀)
  have hsum_lt : (e₁.program.map (·.size)).sum + (e₂.program.map (·.size)).sum < UInt64.size := by
    have := layout.no_overflow
    rw [← Program.map_size_toExecutable_eq (p₁ ++ p₂),
        Program.toExecutable_append_program p₁ p₂ (l := layout.toLayout),
        List.map_append, List.sum_append] at this
    exact this
  have he₂_start : e₂.startAddr = e₁.startAddr + .ofNat ((e₁.program.map (·.size)).sum) := by
    letI := layout.toLayout.take p₁
    rw [Program.map_size_toExecutable_eq p₁]
    rfl
  have happ : (p₁ ++ p₂).toExecutable.withAddresses = e₁.withAddresses ++ e₂.withAddresses :=
    Program.toExecutable_append_withAddresses p₁ p₂ (l := layout.toLayout)
  by_cases h_nil : e₁.withAddresses.dropWhile (·.addr ≠ pc) = []
  · refine ⟨[], ?_, by simp⟩
    dsimp only [Executable.directivesAtAddress]
    rw [happ, dropWhile_append_of_eq_nil h_nil, List.nil_append]
  · obtain ⟨off₁, cs, hcs_mem, hcs_sum, hpc₁, hdrop₁⟩ :=
      dropWhile_withAddresses_ne_nil e₁ pc h_nil
    obtain ⟨off₂, hoff₂, haddr₂⟩ := mem_withAddresses_offset e₂ hy₀_mem
    rw [he₂_start, add_ofNat_add, hy₀_addr] at haddr₂
    have hoff_eq : off₁ = (e₁.program.map (·.size)).sum + off₂ :=
      add_ofNat_inj (by omega) (by omega) (hpc₁.symm.trans haddr₂)
    have hcs_zero : (cs.map (·.size)).sum = 0 := by omega
    have hpc_e₂ : e₂.startAddr = pc := by
      rw [he₂_start, hpc₁]
      congr 1; congr 1; omega
    have hall_pc : ∀ x ∈ Executable.withAddresses {startAddr := pc, program := cs},
        decide (x.addr = pc) = true := fun x hx =>
      decide_eq_true (withAddresses_all_addr_eq_of_sum_zero cs pc hcs_zero x hx)
    have hdrop₂ : e₂.withAddresses.dropWhile (·.addr ≠ pc) = e₂.withAddresses := by
      rcases he₂ : e₂ with ⟨sa₂, prog₂⟩
      rw [he₂] at hpc_e₂
      subst hpc_e₂
      exact Executable.withAddresses_dropWhile_start prog₂ sa₂
    refine ⟨cs, ?_, fun c hc => ?_⟩
    · dsimp only [Executable.directivesAtAddress]
      rw [happ, dropWhile_append_of_ne_nil h_nil, hdrop₁, hdrop₂,
          takeWhile_append_of_all hall_pc, List.map_append,
          Executable.withAddresses_map_snd]
    · refine ⟨?_, size_zero_of_sum_zero hcs_zero hc⟩
      rw [Program.toExecutable_append_program p₁ p₂ (l := layout.toLayout)]
      exact List.mem_append_left _ (hcs_mem c hc)

end Kraken
