module

/-
Omnisemantics for x64.
-/

import Kraken.Attribute
public import Kraken.OmniSemantics
public import Kraken.X64.Semantics

@[expose] public section

open Kraken (Layout WellFormedLayout)

@[kstep] def Effects.All (post : MachineState → Prop) : Effects → Prop
  | .done a => post a
  | .unimplemented _ => False
  | .unresolved_label _ => False
  | .gp_unaligned .. => False
  | .nonmem_load .. => False
  | .nonmem_store .. => False
  | @Effects.undefined α _ cont => ∀ v: α, (cont v).All post
  | .require_read_access _ cont => (cont ()).All post
  | .require_write_access _ cont => (cont ()).All post
  | .require_exec_access _ cont => (cont ()).All post

@[ksimp] theorem Effects.All_require_read_access (addr : BitVec 64) (bytes : UInt64)
    (ok : Unit → Effects) (post : MachineState → Prop) :
    (require_access require_read_access addr bytes ok).All post = (ok ()).All post := by
  dsimp only [require_access]
  split <;> rfl

@[ksimp] theorem Effects.All_require_write_access (addr : BitVec 64) (bytes : UInt64)
    (ok : Unit → Effects) (post : MachineState → Prop) :
    (require_access require_write_access addr bytes ok).All post = (ok ()).All post := by
  dsimp only [require_access]
  split <;> rfl

theorem Effects.All_storeAvx {s : MachineData} {addr : BitVec 64} {w : AvxWidth}
    {v : w.type} {i : Int} {ret : MachineData → Effects} {post : MachineState → Prop}
    {checkAlign : Bool} (ha : checkAlign → isAligned w.bytes addr)
    (h : Mem.loadInt s.dmem addr w.bytes = some i)
    (hk : (ret { s with dmem := Mem.storeInt s.dmem addr w.bytes v.toInt }).All post) :
    (s.storeAvx addr v ret checkAlign).All post := by
  unfold MachineData.storeAvx
  split
  · cases checkAlign <;> simp_all
  rw [Effects.All_require_write_access]
  simp only [h]
  exact hk

theorem Effects.All_loadAvx {s : MachineData} {addr : BitVec 64} {w : AvxWidth} {i : Int}
    {ret : w.type → MachineData → Effects} {post : MachineState → Prop} {checkAlign : Bool}
    (ha : checkAlign → isAligned w.bytes addr)
    (h : Mem.loadInt s.dmem addr w.bytes = some i)
    (hk : (ret (.ofInt _ i) s).All post) :
    (s.loadAvx addr w ret checkAlign).All post := by
  unfold MachineData.loadAvx
  split
  · cases checkAlign <;> simp_all
  rw [Effects.All_require_read_access]
  simp only [h]
  exact hk

def step1 (e : Executable) (s : MachineState) (post : @Post MachineState) : Prop :=
  (Executable.step e s .done).All post

theorem Directives.interp_directivesAtAddress_of_zeroSizePrefix [Labels]
    {p : Program} [l : Layout p] {pc : Int64} {rest : List (Kraken.Sized Directive)}
    (h : Kraken.ZeroSizePrefix (p.toExecutable.directivesAtAddress pc) rest)
    (s : MachineData) (ret : Int64 → MachineData → Effects) :
    Directives.interp (p.toExecutable.directivesAtAddress pc) s pc ret =
      Directives.interp rest s pc ret := by
  obtain ⟨pre, hpre, hz⟩ := h
  rw [hpre]
  have hmem := fun c (hc : c ∈ pre) => Kraken.Program.mem_of_zeroSizePrefix hpre hz hc
  clear hpre hz
  induction pre generalizing s with
  | nil => rfl
  | cons c pre ih =>
    obtain ⟨m, d', hd', rfl, hz0⟩ := hmem c List.mem_cons_self
    simp only [List.cons_append, Directives.interp, Int64.reduceOfNat, Int64.add_zero,
      inert_of_size_zero hd' hz0]
    exact ih s (fun c' hc' => hmem c' (List.mem_cons_of_mem _ hc'))

theorem eventually_of_interp {p : Program} [l : WellFormedLayout p]
    {k : Nat} {d : Directive} (hd : p[k]? = some d) {post : @Post MachineState} {s : MachineData}
    (h : letI := Executable.labels p.toExecutable
      (d.interp s
        ⟨p.toExecutable.addrOf k, p.toExecutable.addrOf (k + 1)⟩
        (fun s' => .done ⟨s', p.toExecutable.addrOf (k + 1)⟩)
        (fun a s' => .done ⟨s', a⟩)).All post) :
    Eventually (step1 p.toExecutable) post ⟨s, p.toExecutable.addrOf k⟩ := by
  have hc : p.toExecutable.program[k]? = some {directive := d, size := l.size k} := by
    simp [Kraken.Layout.apply_getElem?, hd]
  have hsucc := p.toExecutable.addrOf_succ hc
  letI : Labels := Executable.labels p.toExecutable
  match hsize : l.size k with
  | 0 =>
    apply Eventually.done
    simpa [hsucc, hsize, inert_of_size_zero hd hsize, Effects.All] using h
  | _ + 1 =>
    refine .step _ post ?_ fun _ => .done _
    unfold step1 Executable.step
    dsimp only
    rw [Directives.interp_directivesAtAddress_of_zeroSizePrefix
      (Kraken.Program.directivesAtAddress_addrOf p hd (by grind only))]
    simpa [Directives.interp, hsucc, hsize] using h

@[ksimp] theorem Int64.add_sub_cancel_left (a b : Int64) : a + (b - a) = b := by grind
@[ksimp] theorem Int64.ofBitVec_toBitVec_ksimp (a : Int64) : Int64.ofBitVec a.toBitVec = a :=
  Int64.ofBitVec_toBitVec a

theorem step_at {p : Program} [WellFormedLayout p] {k : Nat} {d : Directive}
    (hd : p[k]? = some d) {post : @Post MachineState} {s : MachineData}
    (h : letI := Executable.labels p.toExecutable
      (d.interp s
        ⟨p.toExecutable.addrOf k, p.toExecutable.addrOf (k + 1)⟩
        (fun s' => .done ⟨s', p.toExecutable.addrOf (k + 1)⟩)
        (fun a s' => .done ⟨s', a⟩)).All (Eventually (step1 p.toExecutable) post)) :
    Eventually (step1 p.toExecutable) post ⟨s, p.toExecutable.addrOf k⟩ :=
  eventually_trans _ _ _ _ (eventually_of_interp hd h) fun _ => id

theorem label?_eq_some_addrOf {p : Program} [l : Layout p] {lbl : Label} {k : Nat}
    (hk : p.findIdx? (·.isLabel lbl) = some k) :
    @Labels.label? (Executable.labels p.toExecutable) lbl = some (p.toExecutable.addrOf k) :=
  Kraken.Layout.withAddresses_findSome?_label p lbl hk

theorem label?_restrict_eq_some_addrOf {p : Program} [l : Layout p] {ls : List Label}
    {lbl : Label} {k : Nat}
    (hmem : lbl ∈ ls) (hk : p.findIdx? (·.isLabel lbl) = some k) :
    @Labels.label? (@Labels.restrict ls (Executable.labels p.toExecutable)) lbl =
      some (p.toExecutable.addrOf k) := by
  unfold Labels.restrict
  simp [hmem, label?_eq_some_addrOf hk]

/-- `L₁ ⊆ L₂` means every label resolved by `L₁` resolves to the same address in `L₂`. -/
instance : HasSubset Labels where
  Subset L₁ L₂ := ∀ l a, L₁.label? l = some a → L₂.label? l = some a

theorem Labels.check_resolves {L : Labels} {ls : List Label} {k : Unit → Effects}
    {post : MachineState → Prop} (h : (@Labels.check L ls k).All post) :
    ∀ l ∈ ls, (L.label? l).isSome := by
  induction ls with
  | nil => simp
  | cons l ls ih =>
    unfold Labels.check at h
    cases hl : L.label? l with
    | none => simp only [hl, Effects.All] at h
    | some _ =>
      simp only [hl] at h
      simpa [hl] using ih h

/-- If an instruction makes progress, every label it mentions resolves. -/
theorem Directive.usedLabels_resolve {L : Labels} {d : Directive} {s : MachineData}
    {p : Std.Rco Int64} {next : MachineData → Effects} {jmp : Int64 → MachineData → Effects}
    {post : MachineState → Prop} (h : (@Directive.interp L d s p next jmp).All post) :
    ∀ l ∈ d.usedLabels, (L.label? l).isSome := by
  cases d with
  | instr _ =>
    intro l hl
    dsimp only [Directive.interp] at h
    have : (if l ∈ _ then L.label? l else none).isSome := Labels.check_resolves h l hl
    simpa only [hl, ↓reduceIte] using this
  | _ => simp

theorem Labels.restrict_eq_of_subset {L₁ L₂ : Labels} (hL : L₁ ⊆ L₂) {ls : List Label}
    (h : ∀ l ∈ ls, (L₁.label? l).isSome) : @Labels.restrict ls L₁ = @Labels.restrict ls L₂ := by
  unfold Labels.restrict
  congr 1
  funext l
  by_cases hl : l ∈ ls
  · obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (h l hl)
    simp [hl, ha, hL l a ha]
  · simp [hl]

theorem Directive.interp_mono' {L₁ L₂ : Labels} {d : Directive}
    (hL : @Labels.restrict d.usedLabels L₁ = @Labels.restrict d.usedLabels L₂)
    {s : MachineData} {p : Std.Rco Int64}
    {next : MachineData → Effects} {jmp : Int64 → MachineData → Effects} :
    @Directive.interp L₁ d s p next jmp = @Directive.interp L₂ d s p next jmp := by
  cases d with
  | instr _ =>
    dsimp [Directive.interp]
    rw [hL]
  | _ => rfl

theorem label?_eq_some_mem {p : Program} [Kraken.Layout p] {l : Label} {a : Int64}
    (h : (Executable.labels p.toExecutable).label? l = some a) : l ∈ Kraken.Program.labels p := by
  obtain ⟨x, hx, hfx⟩ := List.exists_of_findSome?_eq_some h
  have hd : x.directive = .label l := by rcases x with ⟨d, _, _⟩; dsimp only at hfx; split at hfx <;> simp_all
  have hmem : Kraken.Directive.label l ∈ p :=
    Kraken.Program.map_directive_withAddresses p ▸ hd ▸ List.mem_map_of_mem (f := (·.directive)) hx
  exact List.mem_filterMap.mpr ⟨.label l, hmem, rfl⟩

theorem labels_append_left_subset (p₁ p₂ : Program) [layout : Kraken.Layout (p₁ ++ p₂)] :
    letI := layout.take p₁
    Executable.labels p₁.toExecutable ⊆ Executable.labels (p₁ ++ p₂).toExecutable := by
  intro lbl a ha
  change List.findSome? _ _ = some a at ha ⊢
  rw [Kraken.Program.toExecutable_append_withAddresses p₁ p₂ (l := layout), List.findSome?_append, ha]
  rfl

theorem labels_append_right_subset (p₁ p₂ : Program) [layout : Kraken.WellFormedLayout (p₁ ++ p₂)] :
    letI := layout.drop p₁
    Executable.labels p₂.toExecutable ⊆ Executable.labels (p₁ ++ p₂).toExecutable := by
  intro lbl a ha
  change List.findSome? _ _ = some a at ha ⊢
  rw [Kraken.Program.toExecutable_append_withAddresses p₁ p₂ (l := layout.toLayout),
    List.findSome?_append]
  cases h₁ : List.findSome? _ (letI := layout.toLayout.take p₁; p₁.toExecutable).withAddresses with
  | none => exact ha
  | some _ =>
    have hmem₁ : lbl ∈ Kraken.Program.labels p₁ := by
      letI := layout.toLayout.take p₁; exact label?_eq_some_mem h₁
    have hmem₂ : lbl ∈ Kraken.Program.labels p₂ := by
      letI := layout.toLayout.drop p₁; exact label?_eq_some_mem ha
    have hnodup : (Kraken.Program.labels p₁ ++ Kraken.Program.labels p₂).Nodup := by
      simpa [Kraken.Program.labels, List.filterMap_append] using layout.unique_labels
    exact absurd rfl ((List.nodup_append.mp hnodup).2.2 lbl hmem₁ lbl hmem₂)

theorem Eventually.mono_of_zeroSizePrefix {p q : Program} [WellFormedLayout p] [Layout q]
    (hlabels : Executable.labels p.toExecutable ⊆ Executable.labels q.toExecutable)
    (hdirs : ∀ pc, Kraken.Program.ContainsAddr p pc →
      Kraken.ZeroSizePrefix (q.toExecutable.directivesAtAddress pc)
        (p.toExecutable.directivesAtAddress pc))
    {post : MachineState → Prop} {init : MachineState}
    (h : Eventually (step1 p.toExecutable) post init) :
    Eventually (step1 q.toExecutable) post init := by
  induction h with
  | done s hp => exact .done s hp
  | step s mid_p hstep _ ih =>
    dsimp only [step1, Executable.step] at hstep
    by_cases hpc : Kraken.Program.ContainsAddr p s.pc
    · refine .step s mid_p ?_ ih
      dsimp only [step1, Executable.step]
      rw [@Directives.interp_directivesAtAddress_of_zeroSizePrefix (Executable.labels q.toExecutable)
        _ _ _ _ (hdirs s.pc hpc)]
      by_cases hpos : ∃ c ∈ p.toExecutable.directivesAtAddress s.pc, 0 < c.size
      · -- A single directive runs; its continuations do not depend on the labels.
        obtain ⟨c, hc, hsz⟩ := hpos
        obtain ⟨i, rfl, haddr⟩ := Kraken.Program.mem_directivesAtAddress p hc
        have hz := Kraken.Program.directivesAtAddress_addrOf p (List.getElem?_eq_getElem i.isLt) hsz
        rw [← haddr] at hstep ⊢
        rw [@Directives.interp_directivesAtAddress_of_zeroSizePrefix (Executable.labels p.toExecutable)
          _ _ _ _ hz] at hstep
        rw [@Directives.interp_directivesAtAddress_of_zeroSizePrefix (Executable.labels q.toExecutable)
          _ _ _ _ hz]
        simp only [Directives.interp] at hstep ⊢
        rw [← Directive.interp_mono'
          (Labels.restrict_eq_of_subset hlabels (Directive.usedLabels_resolve hstep))]
        exact hstep
      · have h0 : Kraken.ZeroSizePrefix (p.toExecutable.directivesAtAddress s.pc) [] :=
          ⟨_, by simp, fun c hc => Classical.byContradiction fun hz =>
            hpos ⟨c, hc, Nat.pos_of_ne_zero hz⟩⟩
        rw [@Directives.interp_directivesAtAddress_of_zeroSizePrefix (Executable.labels p.toExecutable)
          _ _ _ _ h0] at hstep
        rw [@Directives.interp_directivesAtAddress_of_zeroSizePrefix (Executable.labels q.toExecutable)
          _ _ _ _ h0]
        simpa only [Directives.interp] using hstep
    · have hall0 : Kraken.ZeroSizePrefix (p.toExecutable.directivesAtAddress s.pc) [] :=
        ⟨p.toExecutable.directivesAtAddress s.pc, by simp,
          fun c hc => Classical.byContradiction fun hz =>
            hpc (Kraken.Program.containsAddr_of_mem_directivesAtAddress p hc (Nat.pos_of_ne_zero hz))⟩
      rw [@Directives.interp_directivesAtAddress_of_zeroSizePrefix (Executable.labels p.toExecutable)
        _ _ _ _ hall0] at hstep
      simp only [Directives.interp, Effects.All] at hstep
      exact ih ⟨s.data, s.pc⟩ hstep

theorem Eventually.append_left (p₁ p₂ : Program) [layout : Kraken.WellFormedLayout (p₁ ++ p₂)]
    (post : MachineState → Prop) (init : MachineState)
    (h : letI := layout.take p₁
         Eventually (step1 p₁.toExecutable) post init) :
    Eventually (step1 (p₁ ++ p₂).toExecutable) post init :=
  letI := layout.take p₁
  Eventually.mono_of_zeroSizePrefix (labels_append_left_subset p₁ p₂)
    (fun pc hpc => ⟨[], by rw [Kraken.Program.directivesAtAddress_append_left p₁ p₂ pc hpc]; rfl, by simp⟩) h

theorem Eventually.append_right (p₁ p₂ : Program) [layout : Kraken.WellFormedLayout (p₁ ++ p₂)]
    (post : MachineState → Prop) (init : MachineState)
    (h : letI := layout.drop p₁
         Eventually (step1 p₂.toExecutable) post init) :
    Eventually (step1 (p₁ ++ p₂).toExecutable) post init :=
  letI := layout.drop p₁
  Eventually.mono_of_zeroSizePrefix (labels_append_right_subset p₁ p₂)
    (Kraken.Program.directivesAtAddress_append_right p₁ p₂) h
