module

import Kraken.Attribute
public import Kraken.Data.List.Infix
public import Kraken.Semantics

@[expose] public section

/-!
# Common Kraken Temporal Logic and Omni-Semantics

Temporal logic (`Eventually`), traced and constant-time execution (`TracedEventually`, `CtEventually`),
loop rules, effect monotonicity (`Effects.onNext_mono`), host program validity (`Host`), and program/block
specifications (`Spec`, `Exec`, `ExecSpec`).
-/

/-! ### Temporal Logic (`Eventually`) and Loop Rules -/

abbrev Post {State : Type} := State → Prop

-- NOTE: 'initial' cannot be moved to the left of the colon as a parameter
-- because it varies in the recursive call in the 'step' constructor (it becomes 'mid').
inductive Eventually {State : Type} (trans : State → Post → Prop) (post : Post) : Post
  | done (initial: State):
      post initial →
      Eventually trans post initial
  | step (initial: State):
      (mid_p: Post) →
      trans initial mid_p →
      (forall (mid: State), mid_p mid → Eventually trans post mid) →
      Eventually trans post initial

theorem step_cps {State : Type} (trans : State → Post → Prop) (post : Post) (initial : State) :
  trans initial (fun mid => Eventually trans post mid) → Eventually trans post initial :=
  by
    intro h
    exact .step initial _ h (fun _ => id)

theorem eventually_trans {State : Type} (trans : State → Post → Prop) (p q : Post) (initial : State)
  (e : Eventually trans p initial)
  (h : ∀ s, p s → Eventually trans q s) :
    Eventually trans q initial
  := by
    induction e with
    | done initial hp => exact h initial hp
    | step initial mid_p ht _ ih => exact .step initial mid_p ht ih

theorem eventually_weaken {State : Type} (trans : State → Post → Prop) (p q : Post) (initial : State)
  (h : ∀ s, p s → q s) :
    Eventually trans p initial → Eventually trans q initial
  := by
    exact fun hp => eventually_trans trans p q initial hp fun s hs => .done s (h s hs)

theorem Eventually.bind {State : Type} {trans : State → Post → Prop} {p q : Post} {s : State}
    (h₁ : Eventually trans p s) (h₂ : ∀ s', p s' → Eventually trans q s') :
    Eventually trans q s :=
  eventually_trans trans p q s h₁ h₂

-- Tailrec-style loop rule
-- Adapted from: https://github.com/mit-plv/bedrock2/blob/8ec2c459bbf16d6cf2baa7d433ae211a243b1011/bedrock2/src/bedrock2/Loops.v#L48
-- This version moves the choice inside the Eventually postcondition.
theorem tailrec_loop {State Measure : Type _} {Ghost : Sort _}
  (trans : State → Post → Prop) (post : Post) (initial : State)
  (P Q : Measure → Ghost → Post)
  (lt : Measure → Measure → Prop)
  (Hwf : WellFounded lt)
  (v0 : Measure) (g0 : Ghost) :
  P v0 g0 initial →
  (∀ v g state, P v g state →
    Eventually trans (fun mid_s =>
      (Q v g mid_s) ∨
      (∃ v' g', P v' g' mid_s ∧ lt v' v ∧ (∀ t_s, Q v' g' t_s → Q v g t_s))
    ) state) →
  (∀ state, Q v0 g0 state → post state) →
  Eventually trans post initial := by
  intro hP hbody hpost
  have h_general : ∀ v g state, P v g state → (∀ t_s, Q v g t_s → Q v0 g0 t_s) → Eventually trans post state := by
    intro v
    induction v using Hwf.induction with
    | h v ih =>
      intro g state hP_state hQ_impl
      have hstep := hbody v g state hP_state
      apply eventually_trans trans _ post state hstep
      intro mid_state h_mid
      match h_mid with
      | .inl hQ =>
        apply Eventually.done
        apply hpost
        apply hQ_impl
        apply hQ
      | .inr ⟨v', ⟨g', ⟨hP_mid, hlt, hQ_impl'⟩⟩⟩ =>
        apply ih v' hlt g' mid_state hP_mid
        intro t_s hQ_t
        apply hQ_impl
        apply hQ_impl'
        apply hQ_t
  apply h_general v0 g0 initial hP
  intro t_s hQ_t
  apply hQ_t

theorem tailrec_loop_cps {State Measure : Type _} {Ghost : Sort _}
  (trans : State → Post → Prop) (post : Post) (initial : State)
  (P Q : Measure → Ghost → Post)
  (lt : Measure → Measure → Prop)
  (Hwf : WellFounded lt)
  (v0 : Measure) (g0 : Ghost) :
  Eventually trans (fun mid_s => Q v0 g0 mid_s ∨ P v0 g0 mid_s) initial →
  (∀ v g state, P v g state →
    Eventually trans (fun mid_s =>
      (Q v g mid_s) ∨
      (∃ v' g', P v' g' mid_s ∧ lt v' v ∧ (∀ t_s, Q v' g' t_s → Q v g t_s))
    ) state) →
  (∀ state, Q v0 g0 state → Eventually trans post state) →
  Eventually trans post initial := by
  intro hinit hbody hpost
  refine eventually_trans trans _ post initial hinit ?_
  rintro mid_s (hQ | hP)
  · exact hpost mid_s hQ
  · exact eventually_trans trans (Q v0 g0) post mid_s
      (tailrec_loop trans (Q v0 g0) mid_s P Q lt Hwf v0 g0 hP hbody (fun _ h => h))
      hpost

/-- `tailrec_loop_cps` specialised to a loop starting at the cut-point (`initial` already satisfies
`P v0 g0`) and a postcondition that does not depend on the measure or the ghost state: the loop body
either reaches `post` directly or re-establishes the invariant `P` at a smaller measure. This
removes the duplicated `Q` and the trivial `∀ t, Q → Q` obligation. -/
theorem tailrec_loop_simple {State Measure : Type _} {Ghost : Sort _}
  (trans : State → Post → Prop) (post : Post) (initial : State)
  (P : Measure → Ghost → Post)
  (lt : Measure → Measure → Prop)
  (Hwf : WellFounded lt)
  (v0 : Measure) (g0 : Ghost)
  (hinit : P v0 g0 initial)
  (hbody : ∀ v g state, P v g state →
    Eventually trans (fun mid_s => post mid_s ∨ ∃ v' g', P v' g' mid_s ∧ lt v' v) state) :
  Eventually trans post initial :=
  tailrec_loop_cps trans post initial P (fun _ _ => post) lt Hwf v0 g0
    (.done initial (.inr hinit))
    (fun v g state hP =>
      eventually_weaken trans _ _ state
        (fun _ h => h.elim Or.inl (fun ⟨v', g', hP', hlt⟩ => Or.inr ⟨v', g', hP', hlt, fun _ h => h⟩))
        (hbody v g state hP))
    (fun s h => .done s h)

/-! ### Leakage Traces and `Effects.All` -/

inductive StepResult (MD : Type)
  | done (a : Kraken.MachineState MD)
  | next (s : MD)

abbrev TracedPost (MD : Type) := StepResult MD → List LeakageEvent → Prop

@[reducible, kstep] def TracedPost.ofPost {MD : Type}
    (P : Kraken.MachineState MD → List LeakageEvent → Prop) : TracedPost MD :=
  fun r tr => match r with
  | .done a => P a tr
  | .next _ => False

@[kstep] def TracedPost.prepend {MD : Type} (pfx : List LeakageEvent) (P : TracedPost MD) : TracedPost MD :=
  fun a tr => P a (pfx ++ tr)

@[kstep] def TracedPost.consEvent {MD : Type} (e : LeakageEvent) (P : TracedPost MD) : TracedPost MD :=
  fun a tr => P a (e :: tr)

theorem TracedPost.prepend_cons {MD : Type} (pfx : List LeakageEvent) (e : LeakageEvent) (P : TracedPost MD) :
    (P.prepend pfx).consEvent e = P.prepend (pfx ++ [e]) := by
  funext a tr
  simp [TracedPost.prepend, TracedPost.consEvent]

theorem TracedPost.prepend_append {MD : Type} (pfx₁ pfx₂ : List LeakageEvent) (P : TracedPost MD) :
    (P.prepend pfx₁).prepend pfx₂ = P.prepend (pfx₁ ++ pfx₂) := by
  funext a tr
  simp [TracedPost.prepend, List.append_assoc]

@[simp]
theorem TracedPost.prepend_nil {MD : Type} (P : TracedPost MD) :
    P.prepend [] = P := by
  funext a tr
  simp [TracedPost.prepend]

def LeakageEvent.readAccess (addr : BitVec 64) (bytes : UInt64) : List LeakageEvent :=
  let start : AddressBound := addr.toFin.castSucc
  let stop := start.val + bytes.toNat
  if h : stop ≤ UInt64.size then
    [.read ⟨start, ⟨stop, Nat.lt_succ_of_le h⟩⟩]
  else
    [.read ⟨start, Fin.last UInt64.size⟩,
     .read ⟨0, ⟨stop - UInt64.size, by have := bytes.toNat_lt_size; omega⟩⟩]

def LeakageEvent.writeAccess (addr : BitVec 64) (bytes : UInt64) : List LeakageEvent :=
  let start : AddressBound := addr.toFin.castSucc
  let stop := start.val + bytes.toNat
  if h : stop ≤ UInt64.size then
    [.write ⟨start, ⟨stop, Nat.lt_succ_of_le h⟩⟩]
  else
    [.write ⟨start, Fin.last UInt64.size⟩,
     .write ⟨0, ⟨stop - UInt64.size, by have := bytes.toNat_lt_size; omega⟩⟩]

@[kstep] def TracedPost.prependEvents {MD : Type} : List LeakageEvent → TracedPost MD → TracedPost MD
  | [], P => P
  | e :: es, P => TracedPost.prependEvents es (P.consEvent e)

@[kstep] def Kraken.Effects.All {MD : Type} (post : TracedPost MD) :
    Kraken.Effects MD → Prop
  | .done a => post (.done a) []
  | .next s => post (.next s) []
  | .unimplemented _ => False
  | .unaligned .. => False
  | .nonmem_load .. => False
  | .nonmem_store .. => False
  | @Kraken.Effects.undefined _ α _ cont => ∀ v : α, (cont v).All post
  | .require_read_access span cont =>
      (cont ()).All (post.consEvent (.read span))
  | .require_write_access span cont =>
      (cont ()).All (post.consEvent (.write span))
  | .require_exec_access p cont =>
      (cont ()).All (post.consEvent (.exec p))
  | .require_const_time vals cont =>
      (cont ()).All (post.consEvent (.var_time vals))

theorem Effects.All_mono {MD : Type} (eff : Kraken.Effects MD)
    {P Q : TracedPost MD}
    (hpq : ∀ a tr, P a tr → Q a tr) :
    eff.All P → eff.All Q := by
  induction eff generalizing P Q with
  | done a => exact hpq (.done a) []
  | next s => exact hpq (.next s) []
  | unimplemented _ | unaligned _ _ | nonmem_load _ _ _ _ | nonmem_store _ _ _ _ => exact False.elim
  | undefined cont ih => exact fun h v => ih v (fun a tr => hpq a tr) (h v)
  | require_read_access span cont ih =>
    exact ih () (fun a tr => hpq a (.read span :: tr))
  | require_write_access span cont ih =>
    exact ih () (fun a tr => hpq a (.write span :: tr))
  | require_exec_access p cont ih =>
    exact ih () (fun a tr => hpq a (.exec p :: tr))
  | require_const_time vals cont ih =>
    exact ih () (fun a tr => hpq a (.var_time vals :: tr))

@[ksimp] theorem Effects.All_require_read_access {MD : Type} (addr : BitVec 64) (bytes : UInt64)
    (ok : Unit → Kraken.Effects MD) (post : TracedPost MD) :
    (require_access require_read_access addr bytes ok).All post =
      (ok ()).All (post.prepend (LeakageEvent.readAccess addr bytes)) := by
  dsimp only [require_access, LeakageEvent.readAccess, Kraken.Effects.All,
              TracedPost.consEvent, TracedPost.prepend, List.cons_append, List.nil_append]
  split <;> rfl

@[ksimp] theorem Effects.All_require_write_access {MD : Type} (addr : BitVec 64) (bytes : UInt64)
    (ok : Unit → Kraken.Effects MD) (post : TracedPost MD) :
    (require_access require_write_access addr bytes ok).All post =
      (ok ()).All (post.prepend (LeakageEvent.writeAccess addr bytes)) := by
  dsimp only [require_access, LeakageEvent.writeAccess, Kraken.Effects.All,
              TracedPost.consEvent, TracedPost.prepend, List.cons_append, List.nil_append]
  split <;> rfl

def onNextPost {MD : Type} (post : TracedPost MD)
    (next : MD → Kraken.Effects MD) (jmp : Int64 → MD → Kraken.Effects MD) : TracedPost MD :=
  fun r tr =>
    Kraken.Effects.All (post.prepend tr)
      (match r with
       | .next s => next s
       | .done st => jmp st.pc st.data)

theorem Effects.All_onNext {MD : Type} (eff : Kraken.Effects MD)
    (next : MD → Kraken.Effects MD) (jmp : Int64 → MD → Kraken.Effects MD)
    (post : TracedPost MD) :
    (eff.onNext next jmp).All post =
      eff.All (onNextPost post next jmp) := by
  induction eff generalizing post with
  | next s => rfl
  | done a => rfl
  | unimplemented _ | unaligned _ _ | nonmem_load _ _ _ _ | nonmem_store _ _ _ _ => rfl
  | undefined cont ih =>
    simp only [Kraken.Effects.onNext, Kraken.Effects.All, ih]
  | require_read_access span cont ih => exact ih () _
  | require_write_access span cont ih => exact ih () _
  | require_exec_access p cont ih => exact ih () _
  | require_const_time vals cont ih => exact ih () _

/-! ### Traced and Constant-Time Execution (`TracedEventually`, `CtEventually`) -/

def step1 {Instr Const MD : Type} [ArchDirective (Kraken.Directive Instr Const) MD]
    (e : Kraken.Executable Instr Const) (s : Kraken.MachineState MD)
    (post : @Post (Kraken.MachineState MD)) : Prop :=
  (e.step s .done).All (TracedPost.ofPost fun a _ => post a)

def step1Traced {Instr Const MD : Type} [ArchDirective (Kraken.Directive Instr Const) MD]
    (e : Kraken.Executable Instr Const) (st : Kraken.MachineState MD × List LeakageEvent)
    (post : @Post (Kraken.MachineState MD × List LeakageEvent)) : Prop :=
  (e.step st.1 .done).All (TracedPost.ofPost fun a tr => post (a, st.2 ++ tr))

def TracedGoal {MD : Type} (post : @Post (Kraken.MachineState MD)) (tr : List LeakageEvent) :
    @Post (Kraken.MachineState MD × List LeakageEvent) :=
  fun x => x.2 = tr ∧ post x.1

theorem TracedGoal.done {MD : Type} {post : @Post (Kraken.MachineState MD)}
    {st : Kraken.MachineState MD} {tr : List LeakageEvent} (h : post st) :
    TracedGoal post tr (st, tr) :=
  ⟨rfl, h⟩

def TracedEventually {Instr Const MD : Type} [ArchDirective (Kraken.Directive Instr Const) MD]
    (e : Kraken.Executable Instr Const)
    (post : @Post (Kraken.MachineState MD))
    (tr : List LeakageEvent)
    (st : Kraken.MachineState MD) : Prop :=
  Eventually (step1Traced e) (TracedGoal post tr) (st, [])

theorem TracedEventually.done {Instr Const MD : Type} [ArchDirective (Kraken.Directive Instr Const) MD]
    {e : Kraken.Executable Instr Const} {post : @Post (Kraken.MachineState MD)}
    {st : Kraken.MachineState MD} {tr : List LeakageEvent} (h : post st) :
    Eventually (step1Traced e) (TracedGoal post tr) (st, tr) :=
  Eventually.done (st, tr) ⟨rfl, h⟩

theorem Eventually.traced_shift {Instr Const MD : Type} [ArchDirective (Kraken.Directive Instr Const) MD]
    {e : Kraken.Executable Instr Const}
    {post : @Post (Kraken.MachineState MD × List LeakageEvent)}
    {st : Kraken.MachineState MD} {pfx tr : List LeakageEvent}
    (h : Eventually (step1Traced e) (fun x => post (x.1, pfx ++ x.2)) (st, tr)) :
    Eventually (step1Traced e) post (st, pfx ++ tr) := by
  generalize h_init : ((st, tr) : Kraken.MachineState MD × List LeakageEvent) = init at h
  induction h generalizing st tr with
  | done init hpost =>
    subst h_init
    exact Eventually.done (st, pfx ++ tr) hpost
  | step init mid_p hstep _ ih =>
    subst h_init
    refine Eventually.step (st, pfx ++ tr)
      (fun x => ∃ tr'', x.2 = pfx ++ tr'' ∧ mid_p (x.1, tr'')) ?_ ?_
    · dsimp only [step1Traced] at hstep ⊢
      refine Effects.All_mono _ (fun r tr' hm => ?_) hstep
      cases r with
      | done a => exact ⟨tr ++ tr', by simp [List.append_assoc], hm⟩
      | next s => exact False.elim hm
    · rintro ⟨st', _⟩ ⟨tr'', rfl, hm⟩
      exact ih (st', tr'') hm rfl

theorem TracedEventually.weaken {Instr Const MD : Type} [ArchDirective (Kraken.Directive Instr Const) MD]
    {e : Kraken.Executable Instr Const} {p q : @Post (Kraken.MachineState MD)}
    {tr : List LeakageEvent} {st : Kraken.MachineState MD}
    (h : TracedEventually e p tr st) (hpq : ∀ st', p st' → q st') :
    TracedEventually e q tr st :=
  eventually_weaken (step1Traced e) _ _ (st, [])
    (fun x ⟨htr, hp⟩ => ⟨htr, hpq x.1 hp⟩) h

theorem TracedEventually.bind {Instr Const MD : Type} [ArchDirective (Kraken.Directive Instr Const) MD]
    {e : Kraken.Executable Instr Const} {p q : @Post (Kraken.MachineState MD)}
    {tr₁ tr₂ : List LeakageEvent} {st : Kraken.MachineState MD}
    (h₁ : TracedEventually e p tr₁ st)
    (h₂ : ∀ st', p st' → TracedEventually e q tr₂ st') :
    TracedEventually e q (tr₁ ++ tr₂) st := by
  refine eventually_trans (step1Traced e) _ _ (st, []) h₁ ?_
  rintro ⟨st', tr₁⟩ ⟨rfl, hp⟩
  have h₂' : Eventually (step1Traced e) (fun x => tr₁ ++ x.2 = tr₁ ++ tr₂ ∧ q x.1) (st', []) :=
    eventually_weaken (step1Traced e) _ _ (st', [])
      (fun x ⟨htr, hq⟩ => ⟨by rw [htr], hq⟩) (h₂ st' hp)
  simpa only [List.append_nil] using Eventually.traced_shift (pfx := tr₁) (tr := []) h₂'

/-- Constant-time Hoare triple over a family of secret contexts `sec : Secret`:
there exists a single leakage trace `tr` such that for all `sec : Secret` and
initial states `st` satisfying `pre sec st`, execution reaches `post sec` with trace `tr`. -/
def CtEventually {Instr Const MD : Type} [ArchDirective (Kraken.Directive Instr Const) MD] {Secret : Sort _}
    (e : Kraken.Executable Instr Const)
    (pre post : Secret → @Post (Kraken.MachineState MD)) : Prop :=
  ∃ tr : List LeakageEvent,
    ∀ sec st, pre sec st → TracedEventually e (post sec) tr st

theorem CtEventually.weaken {Instr Const MD : Type} [ArchDirective (Kraken.Directive Instr Const) MD] {Secret : Sort _}
    {e : Kraken.Executable Instr Const} {pre post₁ post₂ : Secret → @Post (Kraken.MachineState MD)}
    (h : CtEventually e pre post₁)
    (himp : ∀ sec st, post₁ sec st → post₂ sec st) :
    CtEventually e pre post₂ := by
  obtain ⟨tr, htr⟩ := h
  exact ⟨tr, fun sec st hpre => (htr sec st hpre).weaken (himp sec)⟩

theorem CtEventually.conseq {Instr Const MD : Type} [ArchDirective (Kraken.Directive Instr Const) MD] {Secret : Sort _}
    {e : Kraken.Executable Instr Const} {pre₁ pre₂ post₁ post₂ : Secret → @Post (Kraken.MachineState MD)}
    (hpre : ∀ sec st, pre₂ sec st → pre₁ sec st)
    (hpost : ∀ sec st, post₁ sec st → post₂ sec st)
    (h : CtEventually e pre₁ post₁) :
    CtEventually e pre₂ post₂ := by
  obtain ⟨tr, htr⟩ := h
  exact ⟨tr, fun sec st hp => (htr sec st (hpre sec st hp)).weaken (hpost sec)⟩

theorem CtEventually.bind {Instr Const MD : Type} [ArchDirective (Kraken.Directive Instr Const) MD] {Secret : Sort _}
    {e : Kraken.Executable Instr Const} {P R Q : Secret → @Post (Kraken.MachineState MD)}
    (h₁ : CtEventually e P R)
    (h₂ : CtEventually e R Q) :
    CtEventually e P Q := by
  obtain ⟨tr₁, h₁⟩ := h₁
  obtain ⟨tr₂, h₂⟩ := h₂
  exact ⟨tr₁ ++ tr₂, fun sec st hp => (h₁ sec st hp).bind (h₂ sec)⟩

theorem forall_prod_curry {α β : Type _} {P : α → β → Prop} :
    (∀ a b, P a b) = (∀ p : α × β, P p.1 p.2) :=
  propext ⟨fun h ⟨a, b⟩ => h a b, fun h a b => h (a, b)⟩

theorem exists_forall_unpack_first {T α β : Type _} {P : T → α × β → Prop} :
    (∃ tr : T, ∀ p : α × β, P tr p) = (∃ tr : T, ∀ (a : α) (b : β), P tr (a, b)) :=
  propext ⟨fun ⟨tr, h⟩ => ⟨tr, fun a b => h (a, b)⟩, fun ⟨tr, h⟩ => ⟨tr, fun ⟨a, b⟩ => h a b⟩⟩

theorem tailrec_loop_traced {Instr Const MD Measure Pub Secret Ghost : Type _}
    [ArchDirective (Kraken.Directive Instr Const) MD]
    (e : Kraken.Executable Instr Const)
    (Inv : Measure → Pub → Prop := fun _ _ => True)
    (P Q : Measure → Pub → Secret → Ghost → @Post (Kraken.MachineState MD))
    (v0 : Measure) (pub0 : Pub)
    (lt : Measure → Measure → Prop := by exact (· < ·))
    (Hwf : WellFounded lt := by exact Nat.lt_wfRel.wf)
    (hInv0 : Inv v0 pub0)
    (hbody : ∀ v pub, Inv v pub →
      (∃ tr_step, ∀ sec g state, P v pub sec g state →
        TracedEventually e (Q v pub sec g) tr_step state) ∨
      (∃ v' pub', lt v' v ∧ Inv v' pub' ∧ ∃ tr_step, ∀ sec g state, P v pub sec g state →
        TracedEventually e (fun mid_s =>
          ∃ g', P v' pub' sec g' mid_s ∧ (∀ t_s, Q v' pub' sec g' t_s → Q v pub sec g t_s)) tr_step state)) :
    ∃ tr_loop, ∀ sec g state, P v0 pub0 sec g state →
      TracedEventually e (Q v0 pub0 sec g) tr_loop state := by
  induction v0 using Hwf.induction generalizing pub0 with
  | h v ih =>
    rcases hbody v pub0 hInv0 with ⟨tr_step, hexit⟩ | ⟨v', pub', hlt, hInv', tr_step, hcont⟩
    · exact ⟨tr_step, hexit⟩
    · obtain ⟨tr_rest, hrest⟩ := ih v' hlt pub' hInv'
      refine ⟨tr_step ++ tr_rest, fun sec g state hP => ?_⟩
      refine (hcont sec g state hP).bind ?_
      rintro mid_s ⟨g', hP', hQ_impl⟩
      exact (hrest sec g' mid_s hP').weaken hQ_impl

theorem tailrec_loop_cps_traced {Instr Const MD Measure Pub Secret Ghost : Type _}
    [ArchDirective (Kraken.Directive Instr Const) MD]
    (e : Kraken.Executable Instr Const)
    (pc : Int64 := e.startAddr)
    {pre : MD → Secret → Prop}
    {post : MD → Secret → @Post (Kraken.MachineState MD)}
    (Inv : Measure → Pub → Prop := fun _ _ => True)
    (P Q : Measure → Pub → MD → Secret → Ghost → @Post (Kraken.MachineState MD))
    (v0 : Measure) (pub0 : Pub)
    (g0 : MD → Secret → Ghost)
    (lt : Measure → Measure → Prop := by exact (· < ·))
    (Hwf : WellFounded lt := by exact Nat.lt_wfRel.wf)
    (hinit :
      (∃ tr_init, ∀ s₀ sec, pre s₀ sec →
        TracedEventually e (Q v0 pub0 s₀ sec (g0 s₀ sec)) tr_init ⟨s₀, pc⟩) ∨
      (Inv v0 pub0 ∧ ∃ tr_init, ∀ s₀ sec, pre s₀ sec →
        TracedEventually e (P v0 pub0 s₀ sec (g0 s₀ sec)) tr_init ⟨s₀, pc⟩))
    (hbody : ∀ v pub, Inv v pub →
      (∃ tr_step, ∀ s₀ sec g state, P v pub s₀ sec g state →
        TracedEventually e (Q v pub s₀ sec g) tr_step state) ∨
      (∃ v' pub', lt v' v ∧ Inv v' pub' ∧ ∃ tr_step, ∀ s₀ sec g state, P v pub s₀ sec g state →
        TracedEventually e (fun mid_s =>
          ∃ g', P v' pub' s₀ sec g' mid_s ∧ (∀ t_s, Q v' pub' s₀ sec g' t_s → Q v pub s₀ sec g t_s)) tr_step state))
    (hpost : ∃ tr_post, ∀ s₀ sec state, Q v0 pub0 s₀ sec (g0 s₀ sec) state →
      TracedEventually e (post s₀ sec) tr_post state) :
    ∃ tr, ∀ s₀ sec, pre s₀ sec → TracedEventually e (post s₀ sec) tr ⟨s₀, pc⟩ := by
  obtain ⟨tr_post, hpost⟩ := hpost
  rcases hinit with ⟨tr_init, hskip⟩ | ⟨hInv0, tr_init, henter⟩
  · exact ⟨tr_init ++ tr_post, fun s₀ sec hI => (hskip s₀ sec hI).bind (hpost s₀ sec)⟩
  · obtain ⟨tr_loop, hloop⟩ :=
      tailrec_loop_traced e Inv
        (fun v pub (s₀, sec) g => P v pub s₀ sec g)
        (fun v pub (s₀, sec) g => Q v pub s₀ sec g)
        v0 pub0 lt Hwf hInv0
        (fun v pub hInv =>
          match hbody v pub hInv with
          | .inl ⟨tr_s, hex⟩ => .inl ⟨tr_s, fun ⟨s₀, sec⟩ g st hP => hex s₀ sec g st hP⟩
          | .inr ⟨v', pub', hlt, hInv', tr_s, hcont⟩ =>
            .inr ⟨v', pub', hlt, hInv', tr_s, fun ⟨s₀, sec⟩ g st hP => hcont s₀ sec g st hP⟩)
    exact ⟨(tr_init ++ tr_loop) ++ tr_post, fun s₀ sec hI =>
      ((henter s₀ sec hI).bind (hloop (s₀, sec) (g0 s₀ sec))).bind (hpost s₀ sec)⟩

/-! ### Monotonicity of `Effects.onNext` -/

theorem Effects.onNext_mono {MD : Type} (eff : Kraken.Effects MD)
    {P Q : TracedPost MD}
    {next₁ next₂ : MD → Kraken.Effects MD}
    {jmp₁ jmp₂ : Int64 → MD → Kraken.Effects MD}
    {pfx : List LeakageEvent}
    (hnext : ∀ s' pfx', (next₁ s').All (P.prepend pfx') → (next₂ s').All (Q.prepend pfx'))
    (hjmp : ∀ a s' pfx', (jmp₁ a s').All (P.prepend pfx') → (jmp₂ a s').All (Q.prepend pfx')) :
    (eff.onNext next₁ jmp₁).All (P.prepend pfx) →
    (eff.onNext next₂ jmp₂).All (Q.prepend pfx) := by
  induction eff generalizing pfx with
  | next s => exact hnext s pfx
  | done a => exact hjmp a.pc a.data pfx
  | unimplemented _ | unaligned _ _ | nonmem_load _ _ _ _ | nonmem_store _ _ _ _ => exact False.elim
  | undefined cont ih => exact fun h v => ih v (h v)
  | require_read_access span cont ih =>
    dsimp only [Kraken.Effects.onNext, Kraken.Effects.All]
    rw [TracedPost.prepend_cons, TracedPost.prepend_cons]
    exact ih ()
  | require_write_access span cont ih =>
    dsimp only [Kraken.Effects.onNext, Kraken.Effects.All]
    rw [TracedPost.prepend_cons, TracedPost.prepend_cons]
    exact ih ()
  | require_exec_access p cont ih =>
    dsimp only [Kraken.Effects.onNext, Kraken.Effects.All]
    rw [TracedPost.prepend_cons, TracedPost.prepend_cons]
    exact ih ()
  | require_const_time vals cont ih =>
    dsimp only [Kraken.Effects.onNext, Kraken.Effects.All]
    rw [TracedPost.prepend_cons, TracedPost.prepend_cons]
    exact ih ()

/-! ### Inert Directives and Host Program Validity (`Host`) -/

/-- `d` is inert if it falls through with the same machine state and no observable effect. -/
def Directive.Inert {D MD : Type} [ArchDirective D MD]
    (d : D) : Prop :=
  ∀ [Labels] (s : MD) (p : Std.Rco Int64)
    (next : MD → Kraken.Effects MD)
    (jmp : Int64 → MD → Kraken.Effects MD)
    (post : TracedPost MD),
    ((ArchDirective.interp d s p).onNext next jmp).All post ↔ (next s).All post

namespace Kraken

/-- Abstract validity assumptions about the `Layout` of a host program `prog`. -/
class Host {Instr Const : Type} {MD : outParam Type} [ArchDirective (Kraken.Directive Instr Const) MD]
    (prog : outParam (List (Kraken.Directive Instr Const))) extends Kraken.Layout Instr Const where
  /-- Any directive that occupies zero space in the executable must be semantically inert. -/
  zero_inert : ∀ i d, prog[i]? = some d → size i = 0 → Directive.Inert d
  /-- Two directives at the same address have the same offset in the executable. -/
  addr_determines_offset : ∀ j k, (toLayout.apply prog).addrOf j = (toLayout.apply prog).addrOf k →
    (toLayout.apply prog).sizeBefore j = (toLayout.apply prog).sizeBefore k

instance {Instr Const MD : Type} [ArchDirective (Kraken.Directive Instr Const) MD]
    {prog : List (Kraken.Directive Instr Const)} :
    CoeFun (Host prog) (fun _ => List (Kraken.Directive Instr Const) → Kraken.Executable Instr Const) where
  coe h := h.toLayout.apply

end Kraken

export Kraken (Host)

namespace Kraken.Host

variable {Instr Const MD : Type} [ArchDirective (Kraken.Directive Instr Const) MD]
  {p : List (Kraken.Directive Instr Const)} [h : Host p]

def prog : List (Kraken.Directive Instr Const) := p

@[instance_reducible]
def layout : Kraken.Layout Instr Const := h.toLayout

def exe : Kraken.Executable Instr Const := h.toLayout.apply p

def addrOf (k : Nat) : Int64 := (h.toLayout.apply p).addrOf k

@[instance_reducible]
def labels : Labels := Kraken.Executable.labels (Host.exe (p := p))

theorem sizeBefore_eq_of_addrOf_eq {j k : Nat}
    (heq : (h.toLayout.apply p).addrOf j = (h.toLayout.apply p).addrOf k) :
    (h.toLayout.apply p).sizeBefore j = (h.toLayout.apply p).sizeBefore k :=
  h.addr_determines_offset j k heq

theorem inert_of_getElem? {i : Nat} {d : Kraken.Directive Instr Const} (hd : p[i]? = some d)
    (hz : h.size i = 0) : Directive.Inert d :=
  h.zero_inert i d hd hz

def startAddr [DecidableEq Instr] [DecidableEq Const] {sub : List (Kraken.Directive Instr Const)} (hinf : sub.IsInfix p) : Int64 :=
  (h.toLayout.apply p).addrOf (sub.infixIdx p hinf)

def endAddr [DecidableEq Instr] [DecidableEq Const] {sub : List (Kraken.Directive Instr Const)} (hinf : sub.IsInfix p) : Int64 :=
  (h.toLayout.apply p).addrOf (sub.infixIdx p hinf + sub.length)

theorem exe_getElem? (i : Nat) :
    (h.toLayout.apply p).program[i]? =
      p[i]?.map (fun d => {directive := d, size := h.size i}) :=
  Kraken.Layout.apply_getElem? p i

theorem addrOf_succ {k : Nat} {d : Kraken.Directive Instr Const} (hd : p[k]? = some d) :
    (h.toLayout.apply p).addrOf (k + 1) =
      (h.toLayout.apply p).addrOf k + .ofNat (h.size k) :=
  Kraken.Executable.addrOf_apply_succ (layout := h.toLayout) hd

theorem inert_of_size_zero {d : Kraken.Directive Instr Const}
    (hmem : {directive := d, size := 0} ∈ (h.toLayout.apply p).program) : Directive.Inert d := by
  obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp hmem
  rw [Kraken.Layout.apply_getElem?] at hm
  obtain ⟨d', hd', h_eq⟩ := Option.map_eq_some_iff.mp hm
  injection h_eq with hd_eq hz_eq
  subst hd_eq
  exact h.zero_inert m d' hd' hz_eq

theorem directivesAtAddress_addrOf {k : Nat} {c : Kraken.Sized (Kraken.Directive Instr Const)}
    (hc : (h.toLayout.apply p).program[k]? = some c) (hz : 0 < c.size) :
    ∃ pre, (h.toLayout.apply p).directivesAtAddress ((h.toLayout.apply p).addrOf k) = pre ++ [c] ∧
      ∀ c ∈ pre, c.size = 0 :=
  Kraken.Executable.directivesAtAddress_addrOf (h.toLayout.apply p) h.addr_determines_offset hc hz

end Kraken.Host

export Kraken.Host (startAddr endAddr)

section
variable {Instr Const MD : Type} [ArchDirective (Kraken.Directive Instr Const) MD]

theorem Directives.interp_inert_append [Labels] {pre rest : List (Kraken.Sized (Kraken.Directive Instr Const))}
    (hpre : ∀ c ∈ pre, c.size = 0 ∧ Directive.Inert c.directive) (s : MD) (pc : Int64)
    (ret : Int64 → MD → Kraken.Effects MD)
    (post : TracedPost MD) :
    (Directives.interp (pre ++ rest) s pc ret).All post ↔
      (Directives.interp rest s pc ret).All post := by
  induction pre generalizing s with
  | nil => rfl
  | cons c pre ih =>
    obtain ⟨hz, hinert⟩ := hpre c List.mem_cons_self
    obtain ⟨d, z⟩ := c
    dsimp only at hz hinert
    subst hz
    have h0 : pc + Int64.ofNat 0 = pc := by simp
    simp only [List.cons_append, Directives.interp, h0]
    rw [hinert]
    exact ih (fun c hc => hpre c (List.mem_cons_of_mem _ hc)) s

variable {prog : List (Kraken.Directive Instr Const)} [layout : Host prog]

theorem Directive.inert_of_size_zero {d : Kraken.Directive Instr Const}
    (h : {directive := d, size := 0} ∈ (layout prog).program) : Directive.Inert d :=
  Kraken.Host.inert_of_size_zero h

theorem eventually_of_getElem? {k : Nat} {d : Kraken.Directive Instr Const}
    (hd_prog : prog[k]? = some d) {post : @Post (Kraken.MachineState MD)} {s : MD}
    (h : ((@ArchDirective.interp _ _ _ (Kraken.Executable.labels (layout prog)) d s
      ⟨(layout prog).addrOf k, (layout prog).addrOf (k + 1)⟩).onNext
      (fun s' => .done ⟨s', (layout prog).addrOf (k + 1)⟩)
      (fun a s' => .done ⟨s', a⟩)).All (TracedPost.ofPost fun mid _ => post mid)) :
    Eventually (step1 (layout prog)) post ⟨s, (layout prog).addrOf k⟩ := by
  have hd : (layout prog).program[k]? = some {directive := d, size := layout.size k} := by
    rw [Kraken.Layout.apply_getElem?, hd_prog]; rfl
  rw [Kraken.Executable.addrOf_apply_succ hd_prog] at h
  rcases Nat.eq_zero_or_pos (layout.size k) with h0 | hz
  · rw [h0] at hd h
    letI := Kraken.Executable.labels (layout prog)
    rw [Directive.inert_of_size_zero (List.mem_of_getElem? hd)] at h
    have h0' : (layout prog).addrOf k + Int64.ofNat 0 = (layout prog).addrOf k := by simp
    rw [h0'] at h
    exact Eventually.done _ h
  · refine Eventually.step _ post ?_ fun _ hb => Eventually.done _ hb
    obtain ⟨pre, hat, hpre⟩ :=
      Kraken.Executable.directivesAtAddress_addrOf (layout prog) layout.addr_determines_offset hd hz
    have hinert : ∀ c ∈ pre, c.size = 0 ∧ Directive.Inert c.directive := fun c hc =>
      ⟨hpre c hc, Directive.inert_of_size_zero (prog := prog) (hpre c hc ▸
        Kraken.Executable.mem_of_mem_directivesAtAddress (hat ▸ List.mem_append_left _ hc))⟩
    letI := Kraken.Executable.labels (layout prog)
    dsimp only [step1, Kraken.Executable.step]
    rw [hat]
    refine (Directives.interp_inert_append hinert _ _ _ _).mpr ?_
    simpa only [Directives.interp] using h

theorem Kraken.Host.eventually_of_interp {k : Nat} {d : Kraken.Directive Instr Const}
    {p : List (Kraken.Directive Instr Const)}
    (hdp : (d :: p).IsInfixAt prog k) {post : @Post (Kraken.MachineState MD)} {s : MD}
    (h : ((@ArchDirective.interp _ _ _ (Kraken.Executable.labels (layout prog)) d s
      ⟨(layout prog).addrOf k, (layout prog).addrOf (k + 1)⟩).onNext
      (fun s' => .done ⟨s', (layout prog).addrOf (k + 1)⟩)
      (fun a s' => .done ⟨s', a⟩)).All (TracedPost.ofPost fun mid _ => post mid)) :
    Eventually (step1 (layout prog)) post ⟨s, (layout prog).addrOf k⟩ :=
  eventually_of_getElem? hdp.cons.1 h

theorem eventually_of_getElem?_traced {k : Nat} {d : Kraken.Directive Instr Const}
    (hd_prog : prog[k]? = some d) {post : @Post (Kraken.MachineState MD × List LeakageEvent)}
    {s : MD} {pfx : List LeakageEvent}
    (h : ((@ArchDirective.interp _ _ _ (Kraken.Executable.labels (layout prog)) d s
      ⟨(layout prog).addrOf k, (layout prog).addrOf (k + 1)⟩).onNext
      (fun s' => .done ⟨s', (layout prog).addrOf (k + 1)⟩)
      (fun a s' => .done ⟨s', a⟩)).All (TracedPost.ofPost fun mid tr => post ⟨mid, pfx ++ tr⟩)) :
    Eventually (step1Traced (layout prog)) post ⟨⟨s, (layout prog).addrOf k⟩, pfx⟩ := by
  have hd : (layout prog).program[k]? = some {directive := d, size := layout.size k} := by
    rw [Kraken.Layout.apply_getElem?, hd_prog]; rfl
  rw [Kraken.Executable.addrOf_apply_succ hd_prog] at h
  rcases Nat.eq_zero_or_pos (layout.size k) with h0 | hz
  · rw [h0] at hd h
    letI := Kraken.Executable.labels (layout prog)
    rw [Directive.inert_of_size_zero (List.mem_of_getElem? hd)] at h
    have h0' : (layout prog).addrOf k + Int64.ofNat 0 = (layout prog).addrOf k := by simp
    rw [h0'] at h
    dsimp only [Kraken.Effects.All, TracedPost.ofPost] at h
    rw [List.append_nil] at h
    exact Eventually.done _ h
  · refine Eventually.step _ post ?_ fun _ hb => Eventually.done _ hb
    obtain ⟨pre, hat, hpre⟩ :=
      Kraken.Executable.directivesAtAddress_addrOf (layout prog) layout.addr_determines_offset hd hz
    have hinert : ∀ c ∈ pre, c.size = 0 ∧ Directive.Inert c.directive := fun c hc =>
      ⟨hpre c hc, Directive.inert_of_size_zero (prog := prog) (hpre c hc ▸
        Kraken.Executable.mem_of_mem_directivesAtAddress (hat ▸ List.mem_append_left _ hc))⟩
    letI := Kraken.Executable.labels (layout prog)
    dsimp only [step1Traced, Kraken.Executable.step]
    rw [hat]
    refine (Directives.interp_inert_append hinert _ _ _ _).mpr ?_
    simpa only [Directives.interp] using h

/-! ### Program and Subprogram Specifications (`Spec`, `Exec`, `ExecSpec`) -/

omit layout in
theorem Eventually.bind_at {e : Kraken.Executable Instr Const} {p q : @Post (Kraken.MachineState MD)}
    {s : MD} {pc pc' : Int64}
    (h₁ : Eventually (step1 e) p ⟨s, pc'⟩) (hpc : pc = pc')
    (h₂ : ∀ s', p s' → Eventually (step1 e) q s') :
    Eventually (step1 e) q ⟨s, pc⟩ :=
  hpc ▸ eventually_trans (step1 e) p q ⟨s, pc'⟩ h₁ h₂

omit layout in
theorem Eventually.bind_at_traced {e : Kraken.Executable Instr Const}
    {p : @Post (Kraken.MachineState MD)}
    {q : @Post (Kraken.MachineState MD × List LeakageEvent)}
    {s : MD} {pc pc' : Int64} {pfx tr₁ : List LeakageEvent}
    (h₁ : TracedEventually e p tr₁ ⟨s, pc'⟩) (hpc : pc = pc')
    (h₂ : ∀ s', p s' → Eventually (step1Traced e) q (s', pfx ++ tr₁)) :
    Eventually (step1Traced e) q (⟨s, pc⟩, pfx) := by
  subst hpc
  have h₁' : Eventually (step1Traced e) (fun x => x.2 = pfx ++ tr₁ ∧ p x.1) (⟨s, pc⟩, pfx) := by
    have hshift := Eventually.traced_shift (pfx := pfx) (tr := [])
      (post := fun x => x.2 = pfx ++ tr₁ ∧ p x.1)
      (eventually_weaken (step1Traced e) _ _ (⟨s, pc⟩, [])
        (fun x ⟨htr, hp⟩ => ⟨by simp [htr], hp⟩) h₁)
    simpa only [List.append_nil] using hshift
  refine eventually_trans (step1Traced e) _ q (⟨s, pc⟩, pfx) h₁' ?_
  rintro ⟨s', _⟩ ⟨rfl, hp⟩
  exact h₂ s' hp

/-- Specification for an `Executable` starting at `pc` (defaulting to `e.startAddr`)
in state `s₀`, optionally tracking a constant-time leakage `trace`, requiring `pre`
and ensuring `post` eventually holds. -/
@[reducible]
def Kraken.Executable.Spec (e : Kraken.Executable Instr Const) (s₀ : MD)
    (pc : Int64 := e.startAddr)
    (trace : Option (List LeakageEvent) := none)
    (pre : Prop := True)
    (post : @Post (Kraken.MachineState MD)) : Prop :=
  match trace with
  | none => pre → Eventually (step1 e) post ⟨s₀, pc⟩
  | some tr => pre → TracedEventually e post tr ⟨s₀, pc⟩

omit layout in
theorem Kraken.Executable.Spec.bind {e : Kraken.Executable Instr Const} {pre : Prop}
    {p q : @Post (Kraken.MachineState MD)} {s : MD} {pc : Int64}
    (h₁ : e.Spec s (pc := pc) (pre := pre) (post := p))
    (h₂ : ∀ s', p s' → Eventually (step1 e) q s')
    (hpre : pre := by trivial) :
    Eventually (step1 e) q ⟨s, pc⟩ :=
  eventually_trans (step1 e) p q ⟨s, pc⟩ (h₁ hpre) h₂

omit layout in
theorem Kraken.Executable.Spec.bind_at {e : Kraken.Executable Instr Const} {pre : Prop}
    {p q : @Post (Kraken.MachineState MD)} {s : MD} {pc pc' : Int64}
    (h₁ : e.Spec s (pc := pc') (pre := pre) (post := p))
    (hpc : pc = pc')
    (h₂ : ∀ s', p s' → Eventually (step1 e) q s')
    (hpre : pre := by trivial) :
    Eventually (step1 e) q ⟨s, pc⟩ :=
  Eventually.bind_at (h₁ hpre) hpc h₂

omit layout in
theorem Kraken.Executable.Spec.bind_traced {e : Kraken.Executable Instr Const} {pre : Prop}
    {p : @Post (Kraken.MachineState MD)}
    {q : @Post (Kraken.MachineState MD × List LeakageEvent)}
    {s : MD} {pc : Int64} {pfx tr₁ : List LeakageEvent}
    (h₁ : e.Spec s (pc := pc) (trace := some tr₁) (pre := pre) (post := p))
    (h₂ : ∀ s', p s' → Eventually (step1Traced e) q (s', pfx ++ tr₁))
    (hpre : pre := by trivial) :
    Eventually (step1Traced e) q (⟨s, pc⟩, pfx) :=
  Eventually.bind_at_traced (h₁ hpre) rfl h₂

omit layout in
theorem Kraken.Executable.Spec.bind_at_traced {e : Kraken.Executable Instr Const} {pre : Prop}
    {p : @Post (Kraken.MachineState MD)}
    {q : @Post (Kraken.MachineState MD × List LeakageEvent)}
    {s : MD} {pc pc' : Int64} {pfx tr₁ : List LeakageEvent}
    (h₁ : e.Spec s (pc := pc') (trace := some tr₁) (pre := pre) (post := p))
    (hpc : pc = pc')
    (h₂ : ∀ s', p s' → Eventually (step1Traced e) q (s', pfx ++ tr₁))
    (hpre : pre := by trivial) :
    Eventually (step1Traced e) q (⟨s, pc⟩, pfx) :=
  Eventually.bind_at_traced (h₁ hpre) hpc h₂

omit layout in
theorem Directives.interp_mono [Labels] (cs : List (Kraken.Sized (Kraken.Directive Instr Const))) (s : MD) (pc : Int64)
    {ret₁ ret₂ : Int64 → MD → Kraken.Effects MD}
    {P Q : TracedPost MD} {pfx : List LeakageEvent}
    (hret : ∀ a s' pfx', (ret₁ a s').All (P.prepend pfx') → (ret₂ a s').All (Q.prepend pfx')) :
    (Directives.interp cs s pc ret₁).All (P.prepend pfx) →
    (Directives.interp cs s pc ret₂).All (Q.prepend pfx) := by
  induction cs generalizing s pc pfx with
  | nil => exact hret pc s pfx
  | cons c cs ih =>
    exact Effects.onNext_mono (ArchDirective.interp c.directive s ⟨pc, pc + .ofNat c.size⟩)
      (fun s' pfx' => ih s' (pc + .ofNat c.size) (pfx := pfx')) hret

/-- Symbolic execution of all directives in an `Executable` starting from `e.startAddr`. -/
def Kraken.Executable.Exec [Labels] (e : Kraken.Executable Instr Const) (s : MD)
    (post : @Post (Kraken.MachineState MD)) : Prop :=
  (Directives.interp e.program s e.startAddr (fun pc s' => .done ⟨s', pc⟩)).All
    (TracedPost.ofPost fun a _ => post a)

/-- Symbolic execution of all directives in an `Executable` starting from `e.startAddr`,
tracking constant-time leakage trace `tr`. -/
def Kraken.Executable.ExecTraced [Labels] (e : Kraken.Executable Instr Const) (s : MD)
    (tr : List LeakageEvent) (post : @Post (Kraken.MachineState MD)) : Prop :=
  (Directives.interp e.program s e.startAddr (fun pc s' => .done ⟨s', pc⟩)).All
    (TracedPost.ofPost fun a tr' => TracedGoal post tr (a, tr'))

/-- Specification for straight-line symbolic execution of all directives in an `Executable`
starting from `e.startAddr` in state `s₀`, optionally tracking a constant-time leakage `trace`,
requiring `pre` and ensuring `post`. -/
@[reducible]
def Kraken.Executable.ExecSpec [Labels] (e : Kraken.Executable Instr Const) (s₀ : MD)
    (trace : Option (List LeakageEvent) := none)
    (pre : Prop := True)
    (post : @Post (Kraken.MachineState MD)) : Prop :=
  match trace with
  | none => pre → e.Exec s₀ post
  | some tr => pre → e.ExecTraced s₀ tr post

omit layout in
theorem Kraken.Executable.Exec.mono [Labels] {e : Kraken.Executable Instr Const} {s : MD}
    {P Q : @Post (Kraken.MachineState MD)}
    (h : e.Exec s P) (hpq : ∀ st, P st → Q st) : e.Exec s Q :=
  Directives.interp_mono e.program s e.startAddr
    (P := TracedPost.ofPost fun a _ => P a) (Q := TracedPost.ofPost fun a _ => Q a) (pfx := [])
    (ret₁ := fun pc s' => .done ⟨s', pc⟩) (ret₂ := fun pc s' => .done ⟨s', pc⟩)
    (fun a s' _ hp => hpq ⟨s', a⟩ hp) h

omit layout in
theorem Kraken.Executable.ExecTraced.mono [Labels] {e : Kraken.Executable Instr Const} {s : MD}
    {tr : List LeakageEvent} {P Q : @Post (Kraken.MachineState MD)}
    (h : e.ExecTraced s tr P) (hpq : ∀ st, P st → Q st) : e.ExecTraced s tr Q :=
  Directives.interp_mono e.program s e.startAddr
    (P := TracedPost.ofPost fun a tr' => TracedGoal P tr (a, tr'))
    (Q := TracedPost.ofPost fun a tr' => TracedGoal Q tr (a, tr')) (pfx := [])
    (ret₁ := fun pc s' => .done ⟨s', pc⟩) (ret₂ := fun pc s' => .done ⟨s', pc⟩)
    (fun a s' _ ⟨htr, hp⟩ => ⟨htr, hpq ⟨s', a⟩ hp⟩) h

theorem step1_cps_slice (k n : Nat) (post : @Post (Kraken.MachineState MD))
    {s : MD} {pc : Int64} (hpc : pc = (layout prog).addrOf k)
    (h : (@Directives.interp _ _ _ (Kraken.Executable.labels (layout prog))
          (((layout prog).program.drop k).take n) s ((layout prog).addrOf k)
          (fun pc s => .done ⟨s, pc⟩)).All
        (TracedPost.ofPost fun mid _ => Eventually (step1 (layout prog)) post mid)) :
    Eventually (step1 (layout prog)) post ⟨s, pc⟩ := by
  subst hpc
  letI := Kraken.Executable.labels (layout prog)
  induction n generalizing k s with
  | zero =>
    simpa only [List.take_zero, Directives.interp, Kraken.Effects.All, TracedPost.ofPost] using h
  | succ n ih =>
    by_cases hk : k < prog.length
    · have hd_prog : prog[k]? = some prog[k] := List.getElem?_eq_getElem hk
      have hd_exe : (layout prog).program[k]? = some {directive := prog[k], size := layout.size k} := by
        rw [Kraken.Layout.apply_getElem?, hd_prog]; rfl
      obtain ⟨hlt_exe, hget_exe⟩ := List.getElem?_eq_some_iff.mp hd_exe
      rw [List.drop_eq_getElem_cons hlt_exe, hget_exe, List.take_succ_cons,
          Directives.interp, ← Kraken.Executable.addrOf_apply_succ hd_prog] at h
      have hstep := Effects.onNext_mono
        (ArchDirective.interp prog[k] s ⟨(layout prog).addrOf k, (layout prog).addrOf (k + 1)⟩)
        (P := TracedPost.ofPost fun mid _ => Eventually (step1 (layout prog)) post mid)
        (Q := TracedPost.ofPost fun mid _ => Eventually (step1 (layout prog)) post mid)
        (pfx := [])
        (next₂ := fun s' => .done ⟨s', (layout prog).addrOf (k + 1)⟩)
        (jmp₂ := fun a s' => .done ⟨s', a⟩)
        (fun s' _ hs' => ih (k + 1) hs')
        (fun _ _ _ ha => ha)
        h
      exact eventually_trans _ _ _ _ (eventually_of_getElem? hd_prog hstep) (fun _ h => h)
    · have hdrop : (layout prog).program.drop k = [] :=
        List.drop_eq_nil_of_le (by simp [Kraken.Layout.apply]; omega)
      simpa only [hdrop, List.take_nil, Directives.interp, Kraken.Effects.All, TracedPost.ofPost] using h

theorem step1_cps_at (k : Nat) (post : @Post (Kraken.MachineState MD))
    {s : MD} {pc : Int64} (hpc : pc = (layout prog).addrOf k)
    (h : (@Directives.interp _ _ _ (Kraken.Executable.labels (layout prog))
          ((layout prog).program.drop k) s ((layout prog).addrOf k)
          (fun pc s => .done ⟨s, pc⟩)).All
        (TracedPost.ofPost fun mid _ => Eventually (step1 (layout prog)) post mid)) :
    Eventually (step1 (layout prog)) post ⟨s, pc⟩ := by
  refine step1_cps_slice k (layout prog).program.length post hpc ?_
  rw [List.take_of_length_le (by simp)]
  exact h

theorem step1_cps (post : @Post (Kraken.MachineState MD))
    (initial : Kraken.MachineState MD)
    (h : (@Directives.interp _ _ _ (Kraken.Executable.labels (layout prog))
          ((layout prog).directivesFromAddress initial.pc) initial.data initial.pc
          (fun pc s => .done ⟨s, pc⟩)).All
        (TracedPost.ofPost fun mid _ => Eventually (step1 (layout prog)) post mid)) :
    Eventually (step1 (layout prog)) post initial := by
  rcases initial with ⟨s, pc⟩
  rcases Kraken.Executable.directivesFromAddress_cases (layout prog) pc with hnil | ⟨j, _, hpc, hdrop⟩
  · simpa only [hnil, Directives.interp, Kraken.Effects.All, TracedPost.ofPost] using h
  · rw [hdrop, ← hpc] at h
    exact step1_cps_at j post hpc.symm h

theorem step1_cps_slice_accum (k n : Nat)
    (post : @Post (Kraken.MachineState MD × List LeakageEvent))
    {s : MD} {pc : Int64} {pfx : List LeakageEvent} (hpc : pc = (layout prog).addrOf k)
    (h : (@Directives.interp _ _ _ (Kraken.Executable.labels (layout prog))
          (((layout prog).program.drop k).take n) s ((layout prog).addrOf k)
          (fun pc s => .done ⟨s, pc⟩)).All
        (TracedPost.prepend pfx (TracedPost.ofPost fun mid tr => Eventually (step1Traced (layout prog)) post ⟨mid, tr⟩))) :
    Eventually (step1Traced (layout prog)) post ⟨⟨s, pc⟩, pfx⟩ := by
  subst hpc
  letI := Kraken.Executable.labels (layout prog)
  induction n generalizing k s pfx with
  | zero =>
    dsimp only [List.take_zero, Directives.interp, Kraken.Effects.All, TracedPost.prepend, TracedPost.ofPost] at h
    simpa only [List.append_nil] using h
  | succ n ih =>
    by_cases hk : k < prog.length
    · have hd_prog : prog[k]? = some prog[k] := List.getElem?_eq_getElem hk
      have hd_exe : (layout prog).program[k]? = some {directive := prog[k], size := layout.size k} := by
        rw [Kraken.Layout.apply_getElem?, hd_prog]; rfl
      obtain ⟨hlt_exe, hget_exe⟩ := List.getElem?_eq_some_iff.mp hd_exe
      rw [List.drop_eq_getElem_cons hlt_exe, hget_exe, List.take_succ_cons,
          Directives.interp, ← Kraken.Executable.addrOf_apply_succ hd_prog] at h
      have hstep := Effects.onNext_mono
        (ArchDirective.interp prog[k] s ⟨(layout prog).addrOf k, (layout prog).addrOf (k + 1)⟩)
        (P := TracedPost.ofPost fun mid tr => Eventually (step1Traced (layout prog)) post (mid, tr))
        (Q := TracedPost.ofPost fun mid tr => Eventually (step1Traced (layout prog)) post (mid, tr))
        (pfx := pfx)
        (next₂ := fun s' => .done ⟨s', (layout prog).addrOf (k + 1)⟩)
        (jmp₂ := fun a s' => .done ⟨s', a⟩)
        (fun s' pfx' hs' => by
          dsimp only [Kraken.Effects.All, TracedPost.prepend, TracedPost.ofPost]
          rw [List.append_nil]
          exact ih (k + 1) hs')
        (fun _ _ pfx' ha => by
          dsimp only [Kraken.Effects.All, TracedPost.prepend, TracedPost.ofPost] at ha ⊢
          simpa only [List.append_nil] using ha)
        h
      have hstep' : ((@ArchDirective.interp _ _ _ (Kraken.Executable.labels (layout prog)) prog[k] s
          ⟨(layout prog).addrOf k, (layout prog).addrOf (k + 1)⟩).onNext
          (fun s' => .done ⟨s', (layout prog).addrOf (k + 1)⟩)
          (fun a s' => .done ⟨s', a⟩)).All
          (TracedPost.ofPost fun mid tr => Eventually (step1Traced (layout prog)) post ⟨mid, pfx ++ tr⟩) := by
        refine Effects.All_mono _ (fun r tr ha => ?_) hstep
        cases r with
        | done a => exact ha
        | next s => exact False.elim ha
      exact eventually_trans _ _ _ _ (eventually_of_getElem?_traced hd_prog hstep') (fun _ h => h)
    · have hdrop : (layout prog).program.drop k = [] :=
        List.drop_eq_nil_of_le (by simp [Kraken.Layout.apply]; omega)
      simpa only [hdrop, List.take_nil, Directives.interp, Kraken.Effects.All,
                  TracedPost.prepend, TracedPost.ofPost, List.append_nil] using h

theorem step1_cps_at_accum (k : Nat)
    (post : @Post (Kraken.MachineState MD × List LeakageEvent))
    {s : MD} {pc : Int64} {pfx : List LeakageEvent} (hpc : pc = (layout prog).addrOf k)
    (h : (@Directives.interp _ _ _ (Kraken.Executable.labels (layout prog))
          ((layout prog).program.drop k) s ((layout prog).addrOf k)
          (fun pc s => .done ⟨s, pc⟩)).All
        (TracedPost.prepend pfx (TracedPost.ofPost fun mid tr => Eventually (step1Traced (layout prog)) post ⟨mid, tr⟩))) :
    Eventually (step1Traced (layout prog)) post ⟨⟨s, pc⟩, pfx⟩ := by
  refine step1_cps_slice_accum k (layout prog).program.length post hpc ?_
  rw [List.take_of_length_le (by simp)]
  exact h

theorem step1_cps_slice_traced (k n : Nat) (post : @Post (Kraken.MachineState MD))
    {tr : List LeakageEvent} {s : MD} {pc : Int64} (hpc : pc = (layout prog).addrOf k)
    (h : (@Directives.interp _ _ _ (Kraken.Executable.labels (layout prog))
          (((layout prog).program.drop k).take n) s ((layout prog).addrOf k)
          (fun pc s => .done ⟨s, pc⟩)).All
        (TracedPost.ofPost fun mid tr_slice =>
          Eventually (step1Traced (layout prog)) (TracedGoal post tr) (mid, tr_slice))) :
    TracedEventually (layout prog) post tr ⟨s, pc⟩ :=
  step1_cps_slice_accum k n (TracedGoal post tr) (pfx := []) hpc h

theorem step1_cps_at_traced (k : Nat) (post : @Post (Kraken.MachineState MD))
    {tr : List LeakageEvent} {s : MD} {pc : Int64} (hpc : pc = (layout prog).addrOf k)
    (h : (@Directives.interp _ _ _ (Kraken.Executable.labels (layout prog))
          ((layout prog).program.drop k) s ((layout prog).addrOf k)
          (fun pc s => .done ⟨s, pc⟩)).All
        (TracedPost.ofPost fun mid tr_slice =>
          Eventually (step1Traced (layout prog)) (TracedGoal post tr) (mid, tr_slice))) :
    TracedEventually (layout prog) post tr ⟨s, pc⟩ := by
  refine step1_cps_slice_traced k (layout prog).program.length post hpc ?_
  rw [List.take_of_length_le (by simp)]
  exact h

theorem step1_cps_traced (post : @Post (Kraken.MachineState MD))
    {tr : List LeakageEvent} (initial : Kraken.MachineState MD)
    (h : (@Directives.interp _ _ _ (Kraken.Executable.labels (layout prog))
          ((layout prog).directivesFromAddress initial.pc) initial.data initial.pc
          (fun pc s => .done ⟨s, pc⟩)).All
        (TracedPost.ofPost fun mid tr_slice =>
          Eventually (step1Traced (layout prog)) (TracedGoal post tr) (mid, tr_slice))) :
    TracedEventually (layout prog) post tr initial := by
  rcases initial with ⟨s, pc⟩
  rcases Kraken.Executable.directivesFromAddress_cases (layout prog) pc with hnil | ⟨j, _, hpc, hdrop⟩
  · simpa only [hnil, Directives.interp, Kraken.Effects.All, TracedPost.ofPost, TracedEventually] using h
  · rw [hdrop, ← hpc] at h
    exact step1_cps_at_traced j post hpc.symm h

theorem Kraken.Executable.Exec.eventually {s : MD} {post : @Post (Kraken.MachineState MD)}
    (h : @Kraken.Executable.Exec _ _ _ _ (Kraken.Executable.labels (layout prog)) (layout prog) s post) :
    Eventually (step1 (layout prog)) post ⟨s, layout.start⟩ := by
  letI := Kraken.Executable.labels (layout prog)
  refine step1_cps_at 0 post (by simp [Kraken.Layout.apply]) ?_
  simpa only [List.drop_zero, Kraken.Executable.addrOf_zero, Kraken.Executable.Exec] using
    h.mono (fun mid hmid => Eventually.done mid hmid)

theorem Kraken.Executable.ExecTraced.eventually {s : MD} {tr : List LeakageEvent}
    {post : @Post (Kraken.MachineState MD)}
    (h : @Kraken.Executable.ExecTraced _ _ _ _ (Kraken.Executable.labels (layout prog)) (layout prog) s tr post) :
    TracedEventually (layout prog) post tr ⟨s, layout.start⟩ := by
  letI := Kraken.Executable.labels (layout prog)
  refine step1_cps_at_traced 0 post (by simp [Kraken.Layout.apply]) ?_
  simpa only [List.drop_zero, Kraken.Executable.addrOf_zero, Kraken.Executable.ExecTraced] using
    Effects.All_mono _ (fun r tr' hmid => by
      cases r with
      | done mid => exact Eventually.done (mid, tr') hmid
      | next s => exact False.elim hmid) h

theorem step1_cps_subprog {sub : List (Kraken.Directive Instr Const)}
    (k : Nat) {s : MD} {pc : Int64} {P : Kraken.Layout Instr Const → @Post (Kraken.MachineState MD)}
    {post : @Post (Kraken.MachineState MD)}
    (hsub : (prog.drop k).take sub.length = sub)
    (hpc : pc = (layout prog).addrOf k)
    (hexec : ∀ [layout' : Kraken.Layout Instr Const] [Labels], (layout' sub).Exec s (P layout'))
    (hcont : ∀ s' pc', P (layout.shift prog k) ⟨s', pc'⟩ →
      Eventually (step1 (layout prog)) post ⟨s', pc'⟩) :
    Eventually (step1 (layout prog)) post ⟨s, pc⟩ := by
  letI := Kraken.Executable.labels (layout prog)
  refine step1_cps_slice k sub.length post hpc ?_
  rw [← Kraken.Layout.program_shift_of_slice layout.toLayout hsub]
  exact (@hexec (layout.shift prog k) _).mono (fun ⟨s', pc'⟩ hp => hcont s' pc' hp)

theorem step1_subprog {sub : List (Kraken.Directive Instr Const)}
    (k : Nat) {s : MD} {pc : Int64} {pre : Prop} {Q post : @Post (Kraken.MachineState MD)}
    (hexec : ∀ [layout' : Kraken.Layout Instr Const] [Labels],
      (layout' sub).ExecSpec s (pre := pre)
        (post := fun st => st.pc = (layout' sub).addrOf sub.length ∧ Q st))
    (hpre : pre := by trivial)
    (hsub : (prog.drop k).take sub.length = sub := by rfl)
    (hpc : pc = (layout prog).addrOf k)
    (hcont : ∀ s', Q ⟨s', (layout prog).addrOf (k + sub.length)⟩ →
      Eventually (step1 (layout prog)) post ⟨s', (layout prog).addrOf (k + sub.length)⟩) :
    Eventually (step1 (layout prog)) post ⟨s, pc⟩ := by
  refine step1_cps_subprog k hsub hpc (fun [layout' : Kraken.Layout Instr Const] [Labels] => hexec hpre) ?_
  rintro s' _ ⟨rfl, hQ⟩
  rw [Kraken.Layout.addrOf_shift_of_slice layout.toLayout hsub (Nat.le_refl _)] at hQ ⊢
  exact hcont s' hQ

theorem step1_cps_subprog_traced {sub : List (Kraken.Directive Instr Const)}
    (k : Nat) {s : MD} {pc : Int64} {pfx : List LeakageEvent}
    {tr_sub : Kraken.Layout Instr Const → Labels → List LeakageEvent}
    {P : Kraken.Layout Instr Const → @Post (Kraken.MachineState MD)}
    {post : @Post (Kraken.MachineState MD × List LeakageEvent)}
    (hsub : (prog.drop k).take sub.length = sub)
    (hpc : pc = (layout prog).addrOf k)
    (hexec : ∀ [layout' : Kraken.Layout Instr Const] [labels' : Labels],
      (layout' sub).ExecTraced s (tr_sub layout' labels') (P layout'))
    (hcont : ∀ s' pc', P (layout.shift prog k) ⟨s', pc'⟩ →
      Eventually (step1Traced (layout prog)) post
        ⟨⟨s', pc'⟩, pfx ++ tr_sub (layout.shift prog k) (Kraken.Executable.labels (layout prog))⟩) :
    Eventually (step1Traced (layout prog)) post ⟨⟨s, pc⟩, pfx⟩ := by
  letI := Kraken.Executable.labels (layout prog)
  refine step1_cps_slice_accum k sub.length post hpc ?_
  rw [← Kraken.Layout.program_shift_of_slice layout.toLayout hsub]
  refine Effects.All_mono _ (fun r tr' h => ?_) (@hexec (layout.shift prog k) _)
  cases r with
  | done a =>
    rcases h with ⟨htr, hp⟩
    dsimp only [TracedPost.prepend, TracedPost.ofPost] at htr ⊢
    subst htr
    exact hcont a.data a.pc hp
  | next s => exact False.elim h

theorem step1_subprog_traced {sub : List (Kraken.Directive Instr Const)}
    (k : Nat) {s : MD} {pc : Int64} {pfx : List LeakageEvent}
    {tr_sub : Kraken.Layout Instr Const → Labels → List LeakageEvent}
    {pre : Prop} {Q : @Post (Kraken.MachineState MD)}
    {post : @Post (Kraken.MachineState MD × List LeakageEvent)}
    (hexec : ∀ [layout' : Kraken.Layout Instr Const] [labels' : Labels],
      (layout' sub).ExecSpec s (trace := some (tr_sub layout' labels')) (pre := pre)
        (post := fun st => st.pc = (layout' sub).addrOf sub.length ∧ Q st))
    (hpre : pre := by trivial)
    (hsub : (prog.drop k).take sub.length = sub := by rfl)
    (hpc : pc = (layout prog).addrOf k)
    (hcont : ∀ s', Q ⟨s', (layout prog).addrOf (k + sub.length)⟩ →
      Eventually (step1Traced (layout prog)) post
        ⟨⟨s', (layout prog).addrOf (k + sub.length)⟩,
         pfx ++ tr_sub (layout.shift prog k) (Kraken.Executable.labels (layout prog))⟩) :
    Eventually (step1Traced (layout prog)) post ⟨⟨s, pc⟩, pfx⟩ := by
  refine step1_cps_subprog_traced k hsub hpc
    (fun [layout' : Kraken.Layout Instr Const] [Labels] => hexec hpre) ?_
  rintro s' _ ⟨rfl, hQ⟩
  rw [Kraken.Layout.addrOf_shift_of_slice layout.toLayout hsub (Nat.le_refl _)] at hQ ⊢
  exact hcont s' hQ

end
