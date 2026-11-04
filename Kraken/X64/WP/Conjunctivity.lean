module

public import Kraken.X64.WP.Def

namespace Executable
variable {e : Executable} {st₀ : MachineState}

open Classical in
theorem StepIn.and {next₁ next₂ jump₁ jump₂ : MachineState → Prop} (h₁ : e.StepIn next₁ jump₁ st₀)
    (h₂ : e.StepIn next₂ jump₂ st₀) :
    e.StepIn (fun u => next₁ u ∧ next₂ u) (fun u => jump₁ u ∧ jump₂ u) st₀ := by
  intro P r j hr hj
  let probe (c : Prop) : Effects :=
    if c then .fallthrough st₀ else .unimplemented ""
  have hprobe (c : Prop) : (probe c).All (fun _ => True) ↔ c := by
    by_cases hc : c <;>
      simp [probe, hc, Effects.All, Trace.All, X64Effects.All.epost,
        Effect.Incl.input, unimplemented]
  have run₁ := h₁ (fun _ => True) (fun s => probe (next₁ ⟨s, e.nextAddr st₀.pc⟩))
    (fun u => probe (jump₁ u)) (fun _ => (hprobe _).mpr) (fun _ => (hprobe _).mpr)
  have run₂ := h₂ (fun _ => True) (fun s => probe (next₂ ⟨s, e.nextAddr st₀.pc⟩))
    (fun u => probe (jump₂ u)) (fun _ => (hprobe _).mpr) (fun _ => (hprobe _).mpr)
  letI := e.labels
  rw [Effects.All, Directives.interp_eq_bind, Trace.All_bind] at run₁ run₂ ⊢
  exact Trace.All.imp₂ X64Effects.All.epost_imp₂ (fun
    | (.fallthrough, st) => fun e₁ e₂ => hr st.data ⟨(hprobe _).mp e₁, (hprobe _).mp e₂⟩
    | (.jump, st) => fun e₁ e₂ => hj st ⟨(hprobe _).mp e₁, (hprobe _).mp e₂⟩) _ run₁ run₂

theorem StepOut.and_map {β : Type} (o : Int64 → Option β)
    {g₁ g₂ g : β → (MachineState → Prop) → MachineData → Prop}
    (hg : ∀ b R₁ R₂ R s, (∀ u, R₁ u → R₂ u → R u) → g₁ b R₁ s → g₂ b R₂ s → g b R s)
    {next₁ next₂ next jump₁ jump₂ jump : MachineState → Prop}
    (hn : ∀ u, next₁ u → next₂ u → next u) (hj : ∀ u, jump₁ u → jump₂ u → jump u) {st₁ : MachineState}
    (h₁ : e.StepOut (fun a => (o a).map g₁) st₀ next₁ jump₁ st₁)
    (h₂ : e.StepOut (fun a => (o a).map g₂) st₀ next₂ jump₂ st₁) :
    e.StepOut (fun a => (o a).map g) st₀ next jump st₁ := by
  unfold StepOut at h₁ h₂ ⊢
  cases ho : o st₁.pc with
  | none =>
    simp only [ho, Option.map_none] at h₁ h₂ ⊢
    exact hj _ h₁ h₂
  | some b =>
    simp only [ho, Option.map_some] at h₁ h₂ ⊢
    by_cases hb : st₁.data.StackBelow st₀.data
    · simp only [hb, ite_true] at h₁ h₂ ⊢
      refine hg b _ _ _ _ (fun u a b => ?_) h₁ h₂
      by_cases hu : u.pc = e.nextAddr st₀.pc ∧ ¬ u.data.StackBelow st₀.data
      · rw [ite_eq_left hu] at a b ⊢
        exact hn _ a b
      · rw [ite_eq_right hu] at a b ⊢
        exact hj _ a b
    · simp only [hb, ite_false] at h₁ h₂ ⊢
      exact hj _ h₁ h₂

theorem StepOver.and_map {β : Type} (o : Int64 → Option β)
    {g₁ g₂ g : β → (MachineState → Prop) → MachineData → Prop}
    (hg : ∀ b R₁ R₂ R s, (∀ u, R₁ u → R₂ u → R u) → g₁ b R₁ s → g₂ b R₂ s → g b R s)
    {next₁ next₂ next jump₁ jump₂ jump : MachineState → Prop}
    (hn : ∀ u, next₁ u → next₂ u → next u) (hj : ∀ u, jump₁ u → jump₂ u → jump u)
    (h₁ : e.StepOver (fun a => (o a).map g₁) next₁ jump₁ st₀)
    (h₂ : e.StepOver (fun a => (o a).map g₂) next₂ jump₂ st₀) :
    e.StepOver (fun a => (o a).map g) next jump st₀ :=
  StepIn.mono (StepIn.and h₁ h₂) (fun u _ h => hn u h.1 h.2)
    fun _ h => StepOut.and_map o hg hn hj h.1 h.2

end Executable

section
variable [Host] [FunDecls]

omit [FunDecls] in
theorem Program.continueAtOwnLabel_and {p : Program} {s : MachineData}
    {c₁ c₂ e₁ e₂ : MachineState → Prop} {u : MachineState}
    (h₁ : p.ContinueAtOwnLabel s c₁ e₁ u) (h₂ : p.ContinueAtOwnLabel s c₂ e₂ u) :
    p.ContinueAtOwnLabel s (fun u => c₁ u ∧ c₂ u) (fun u => e₁ u ∧ e₂ u) u := by
  unfold Program.ContinueAtOwnLabel at h₁ h₂ ⊢
  by_cases hcond : p.IsLabelAddr u.pc ∧ u.data.StackAtOrBelow s
  · rw [ite_eq_left hcond] at h₁ h₂ ⊢; exact ⟨h₁, h₂⟩
  · rw [ite_eq_right hcond] at h₁ h₂ ⊢; exact ⟨h₁, h₂⟩

public theorem Program.wp_and {p : Program} {done₁ done₂ exit₁ exit₂ : MachineState → Prop} {s : MachineData}
    (h₁ : p.wp done₁ exit₁ s) (h₂ : p.wp done₂ exit₂ s) :
    p.wp (fun u => done₁ u ∧ done₂ u) (fun u => exit₁ u ∧ exit₂ u) s := by
  refine Program.wp.induct
    (fun p done exit s => ∀ done' exit' : MachineState → Prop, p.wp done' exit' s →
      p.wp (fun u => done u ∧ done' u) (fun u => exit u ∧ exit' u) s)
    ?_ p done₁ exit₁ s h₁ done₂ exit₂ h₂
  intro p done exit s hw done' exit' hw'
  rw [Program.wp] at hw' ⊢
  intro H
  refine While.and (fun U V y _ hU hV => ?_) (hw H) (hw' H)
  refine Executable.StepOver.and_map FunDecls.at ?_ (fun _ h₁ h₂ => ⟨h₁, h₂⟩)
    (fun _ h₁ h₂ => Program.continueAtOwnLabel_and h₁ h₂) hU hV
  exact fun _ _ _ _ _ hR h₁ h₂ => Program.wp_mono (fun _ h => h.1) (fun u h => hR u h.1 h.2) (h₁ _ _ h₂)

end
