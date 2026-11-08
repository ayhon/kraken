module

/-
Omnisemantics for x64.
-/

import Kraken.Attribute
public import Kraken.OmniSemantics
public import Kraken.X64.Semantics

@[expose] public section

@[kstep] def Effects.All (post : MachineState → Prop) : Effects → Prop
  | .done a => post a
  | .next _ => False
  | .unimplemented _ => False
  | .undefined_label _ => False
  | .gp_unaligned .. => False
  | .nonmem_load .. => False
  | .nonmem_store .. => False
  | @Effects.undefined α _ cont => ∀ v: α, (cont v).All post
  | .require_read_access _ cont => (cont ()).All post
  | .require_write_access _ cont => (cont ()).All post
  | .require_exec_access _ cont => (cont ()).All post

theorem Effects.bind_mono (eff : Effects)
    {k₁ k₂ : MachineData → Effects}
    {post₁ post₂ : MachineState → Prop}
    (hk : ∀ s, (k₁ s).All post₁ → (k₂ s).All post₂)
    (hdone : ∀ st, post₁ st → post₂ st) :
    (eff.bind k₁).All post₁ → (eff.bind k₂).All post₂ := by
  induction eff <;> grind [Effects.bind, Effects.All]

@[ksimp] theorem Effects.bind_require_read_access (addr : BitVec 64) (bytes : UInt64)
    (ok : Unit → Effects) (k : MachineData → Effects) :
    (require_access require_read_access addr bytes ok).bind k =
      require_access require_read_access addr bytes (fun u => (ok u).bind k) := by
  dsimp only [require_access]
  split <;> rfl

@[ksimp] theorem Effects.bind_require_write_access (addr : BitVec 64) (bytes : UInt64)
    (ok : Unit → Effects) (k : MachineData → Effects) :
    (require_access require_write_access addr bytes ok).bind k =
      require_access require_write_access addr bytes (fun u => (ok u).bind k) := by
  dsimp only [require_access]
  split <;> rfl

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

def step1 (e: Executable) (s: MachineState) (post: @Post MachineState) : Prop :=
  (Executable.step e s).All post

theorem Directives.interp_split [Labels]
    (ds1 ds2 : List (Kraken.Sized Directive)) (s : MachineData) (pc : Int64)
    {post₁ post₂ : MachineState → Prop}
    (hdone : ∀ st, post₁ st → post₂ st)
    (hnext : ∀ s',
      (Directives.interp ds2 s' (ds1.foldl (fun p d => p + Int64.ofNat d.size) pc)).All post₁ →
      post₂ ⟨s', ds1.foldl (fun p d => p + Int64.ofNat d.size) pc⟩)
    (h : (Directives.interp (ds1 ++ ds2) s pc).All post₁) :
    (Directives.interp ds1 s pc).All post₂ := by
  induction ds1 generalizing s pc with
  | nil =>
    rw [Directives.interp, List.nil_append] at *
    exact hnext s h
  | cons d tail ih =>
    rw [List.cons_append, Directives.interp] at h
    rw [Directives.interp]
    exact Effects.bind_mono _ (fun s' => ih s' (pc + Int64.ofNat d.size) hnext) hdone h

theorem eventually_step (prog : Program) [WellFormedLayout prog] (st : MachineState) (post : @Post MachineState) :
    (letI := Executable.labels prog.toExecutable
     Directives.interp (prog.toExecutable.directivesFromAddress st.pc) st.data st.pc).All post →
    Eventually (step1 prog.toExecutable) post st := by
  let e := prog.toExecutable
  rcases st with ⟨s, pc⟩
  intro h
  apply step_cps (step1 e) post ⟨s, pc⟩
  dsimp [step1, Executable.step] at *
  letI := Executable.labels e
  rcases Kraken.Executable.directivesFromAddress_split prog pc with h_end | ⟨h_split, h_len⟩
  · rw [h_end, ← List.append_nil (e.directivesAtAddress pc)] at h
    apply Directives.interp_split (e.directivesAtAddress pc) [] s pc
      (post₁ := post) (post₂ := fun mid => Eventually (step1 e) post mid)
      (fun st' hp => Eventually.done st' hp) _ h
    intro s' h_after
    rw [Directives.interp] at h_after
    exact Eventually.done _ h_after
  · rw [h_split] at h
    apply Directives.interp_split (e.directivesAtAddress pc) _ s pc
      (post₁ := post) (post₂ := fun mid => Eventually (step1 e) post mid)
      (fun st' hp => Eventually.done st' hp) _ h
    intro s' h_after
    exact eventually_step prog ⟨s', _⟩ post h_after
termination_by (prog.toExecutable.withAddresses.dropWhile (·.addr ≠ st.pc)).length
decreasing_by exact h_len

theorem eventually_step_cps (prog : Program) [WellFormedLayout prog]
    (st : MachineState) (post : @Post MachineState) :
    (letI := Executable.labels prog.toExecutable
     Directives.interp (prog.toExecutable.directivesFromAddress st.pc) st.data st.pc).All
      (fun mid => Eventually (step1 prog.toExecutable) post mid) →
    Eventually (step1 prog.toExecutable) post st := by
  intro h
  exact eventually_trans (step1 prog.toExecutable) (fun mid => Eventually (step1 prog.toExecutable) post mid) post st
    (eventually_step prog st _ h) (fun _ => id)

/--
`d` is inert if it falls through with the same machine state and no observable effect.

Labels, empty `.byteArray`s, and no-op instructions like `nop` and `mov %rax, %rax` are inert.
-/
def Directive.Inert (d : Directive) : Prop :=
  ∀ [Labels] s p (next : MachineData → Effects) post,
    ((d.interp s p .next (fun a s' => .done ⟨s', a⟩)).bind next).All post ↔ (next s).All post

theorem Directives.interp_inert_append [Labels] {pre rest : List (Kraken.Sized Directive)}
    (hpre : ∀ c ∈ pre, c.size = 0 ∧ c.directive.Inert) (s : MachineData) (pc : Int64)
    (post : @Post MachineState) :
    (Directives.interp (pre ++ rest) s pc).All post ↔ (Directives.interp rest s pc).All post := by
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

/-- `L₁.Le L₂` means every label resolved by `L₁` resolves to the same address in `L₂`. -/
def Labels.Le (L₁ L₂ : Labels) : Prop :=
  ∀ l a, L₁.label? l = some a → L₂.label? l = some a

private def Effects.Le (e₁ e₂ : Effects) : Prop :=
  ∀ (k : MachineData → Effects) (post : MachineState → Prop),
    (e₁.bind k).All post → (e₂.bind k).All post

private theorem Effects.Le.refl (e : Effects) : e.Le e :=
  fun _ _ h => h

private theorem Effects.Le.undefined_choice {α : Type} [NondetSupportingType α]
    {r₁ r₂ : α → Effects} (hr : ∀ v, (r₁ v).Le (r₂ v)) :
    (@Effects.undefined α _ r₁).Le (@Effects.undefined α _ r₂) :=
  fun k post h v => hr v k post (h v)

private theorem Effects.Le.require_exec {p : Std.Rco Int64}
    {r₁ r₂ : Unit → Effects} (hr : (r₁ ()).Le (r₂ ())) :
    (Effects.require_exec_access p r₁).Le (Effects.require_exec_access p r₂) :=
  hr

private theorem MachineData.load_le {s : MachineData} {addr : BitVec 64} {w : Width}
    {r₁ r₂ : w.type → MachineData → Effects} (hr : ∀ v s', (r₁ v s').Le (r₂ v s')) :
    (s.load addr w r₁).Le (s.load addr w r₂) := by
  intro k post
  simp only [MachineData.load, Effects.bind_require_read_access, Effects.All_require_read_access]
  split
  · exact hr _ _ k post
  · exact False.elim

private theorem MachineData.loadAvx_le {s : MachineData} {addr : BitVec 64} {w : AvxWidth}
    {checkAlign : Bool} {r₁ r₂ : w.type → MachineData → Effects}
    (hr : ∀ v s', (r₁ v s').Le (r₂ v s')) :
    (s.loadAvx addr w r₁ checkAlign).Le (s.loadAvx addr w r₂ checkAlign) := by
  intro k post
  dsimp only [MachineData.loadAvx]
  split
  · exact id
  · simp only [Effects.bind_require_read_access, Effects.All_require_read_access]
    split
    · exact hr _ _ k post
    · exact False.elim

private theorem MachineData.store_le {s : MachineData} {addr : BitVec 64} {w : Width} {v : w.type}
    {r₁ r₂ : MachineData → Effects} (hr : ∀ s', (r₁ s').Le (r₂ s')) :
    (s.store addr v r₁).Le (s.store addr v r₂) := by
  intro k post
  simp only [MachineData.store, Effects.bind_require_write_access, Effects.All_require_write_access]
  split
  · exact hr _ k post
  · exact False.elim

private theorem MachineData.storeAvx_le {s : MachineData} {addr : BitVec 64} {w : AvxWidth} {v : w.type}
    {checkAlign : Bool} {r₁ r₂ : MachineData → Effects} (hr : ∀ s', (r₁ s').Le (r₂ s')) :
    (s.storeAvx addr v r₁ checkAlign).Le (s.storeAvx addr v r₂ checkAlign) := by
  intro k post
  dsimp only [MachineData.storeAvx]
  split
  · exact id
  · simp only [Effects.bind_require_write_access, Effects.All_require_write_access]
    split
    · exact hr _ k post
    · exact False.elim

private theorem label_le {L₁ L₂ : Labels} (hL : L₁.Le L₂) (l : Label)
    {r₁ r₂ : Int64 → Effects} (hr : ∀ a, (r₁ a).Le (r₂ a)) :
    (@label L₁ l r₁).Le (@label L₂ l r₂) := by
  intro k post
  dsimp only [label]
  cases h : L₁.label? l with
  | none => exact False.elim
  | some a =>
    rw [hL l a h]
    exact hr a k post

private theorem ConstExpr.interp_le {L₁ L₂ : Labels} (hL : L₁.Le L₂) (e : ConstExpr) (p : Std.Rco Int64)
    {r₁ r₂ : Int64 → Effects} (hr : ∀ v, (r₁ v).Le (r₂ v)) :
    (@ConstExpr.interp L₁ e p r₁).Le (@ConstExpr.interp L₂ e p r₂) := by
  induction e generalizing r₁ r₂ with
  | label l => exact label_le hL l hr
  | int64 i => exact hr i
  | before_current_instruction => exact hr p.lower
  | after_current_instruction => exact hr p.upper
  | add e1 e2 ih1 ih2 => exact ih1 fun v1 => ih2 fun v2 => hr (v1 + v2)
  | sub e1 e2 ih1 ih2 => exact ih1 fun v1 => ih2 fun v2 => hr (v1 - v2)

private theorem AddrExpr.interp_le {L₁ L₂ : Labels} [address_size : AddressSize] (hL : L₁.Le L₂)
    (a : AddrExpr) (s : Reg64s) (p : Std.Rco Int64)
    {r₁ r₂ : BitVec address_size.address_size.bits → Effects}
    (hr : ∀ addr, (r₁ addr).Le (r₂ addr)) :
    (@AddrExpr.interp L₁ _ a s p r₁).Le (@AddrExpr.interp L₂ _ a s p r₂) :=
  ConstExpr.interp_le hL a.disp p fun _ => hr _

private theorem RegOrMem.interp_le {L₁ L₂ : Labels} [AddressSize] {w : Width} (hL : L₁.Le L₂)
    (o : RegOrMem w) (s : MachineData) (p : Std.Rco Int64)
    {r₁ r₂ : w.type → MachineData → Effects} (hr : ∀ v s', (r₁ v s').Le (r₂ v s')) :
    (@RegOrMem.interp w L₁ _ o s p r₁).Le (@RegOrMem.interp w L₂ _ o s p r₂) := by
  cases o with
  | reg _ => exact hr _ _
  | mem a => exact AddrExpr.interp_le hL a s.regs p fun _ => MachineData.load_le hr

private theorem AvxRegOrMem.interp_le {L₁ L₂ : Labels} [AddressSize] {w : AvxWidth} (hL : L₁.Le L₂)
    (o : AvxRegOrMem w) (s : MachineData) (p : Std.Rco Int64) {checkAlign : Bool}
    {r₁ r₂ : w.type → MachineData → Effects} (hr : ∀ v s', (r₁ v s').Le (r₂ v s')) :
    (@AvxRegOrMem.interp w L₁ _ o s p r₁ checkAlign).Le (@AvxRegOrMem.interp w L₂ _ o s p r₂ checkAlign) := by
  cases o with
  | avx _ => exact hr _ _
  | mem a => exact AddrExpr.interp_le hL a s.regs p fun _ => MachineData.loadAvx_le hr

private theorem MachineData.set_le {L₁ L₂ : Labels} [AddressSize] {w : Width} (hL : L₁.Le L₂)
    (s : MachineData) (d : Dst w) (v : w.type) (p : Std.Rco Int64)
    {r₁ r₂ : MachineData → Effects} (hr : ∀ s', (r₁ s').Le (r₂ s')) :
    (@MachineData.set w L₁ _ s d v p r₁).Le (@MachineData.set w L₂ _ s d v p r₂) := by
  cases d with
  | reg _ => exact hr _
  | mem a => exact AddrExpr.interp_le hL a s.regs p fun _ => MachineData.store_le hr

private theorem MachineData.setAvx_le {L₁ L₂ : Labels} [AddressSize] {aw : AvxWidth} (hL : L₁.Le L₂)
    (s : MachineData) (d : AvxDst aw) (v : aw.type) (p : Std.Rco Int64) {checkAlign : Bool}
    {r₁ r₂ : MachineData → Effects} (hr : ∀ s', (r₁ s').Le (r₂ s')) :
    (@MachineData.setAvx aw L₁ _ s d v p r₁ checkAlign).Le (@MachineData.setAvx aw L₂ _ s d v p r₂ checkAlign) := by
  cases d with
  | avx _ => exact hr _
  | mem a => exact AddrExpr.interp_le hL a s.regs p fun _ => MachineData.storeAvx_le hr

private theorem MachineData.setAvxLegacy_le {L₁ L₂ : Labels} [AddressSize] {w : AvxWidth} (hL : L₁.Le L₂)
    (s : MachineData) (d : AvxDst w) (v : w.type) (p : Std.Rco Int64) {checkAlign : Bool}
    {r₁ r₂ : MachineData → Effects} (hr : ∀ s', (r₁ s').Le (r₂ s')) :
    (@MachineData.setAvxLegacy w L₁ _ s d v p r₁ checkAlign).Le (@MachineData.setAvxLegacy w L₂ _ s d v p r₂ checkAlign) := by
  cases d with
  | avx _ => exact hr _
  | mem a => exact AddrExpr.interp_le hL a s.regs p fun _ => MachineData.storeAvx_le hr

private theorem Operand.interp_le {L₁ L₂ : Labels} [AddressSize] {w : Width} (hL : L₁.Le L₂)
    (o : Operand w) (s : MachineData) (p : Std.Rco Int64)
    {r₁ r₂ : w.type → MachineData → Effects} (hr : ∀ v s', (r₁ v s').Le (r₂ v s')) :
    (@Operand.interp w L₁ _ o s p r₁).Le (@Operand.interp w L₂ _ o s p r₂) := by
  cases o with
  | regOrMem rm => exact RegOrMem.interp_le hL rm s p hr
  | imm v => exact ConstExpr.interp_le hL v p fun _ => hr _ _

private theorem AvxOperand.interp_le {L₁ L₂ : Labels} [AddressSize] {aw : AvxWidth} (hL : L₁.Le L₂)
    (o : AvxOperand aw) (s : MachineData) (p : Std.Rco Int64) {checkAlign : Bool}
    {r₁ r₂ : aw.type → MachineData → Effects} (hr : ∀ v s', (r₁ v s').Le (r₂ v s')) :
    (@AvxOperand.interp aw L₁ _ o s p r₁ checkAlign).Le (@AvxOperand.interp aw L₂ _ o s p r₂ checkAlign) := by
  cases o with
  | regOrMem rm => exact AvxRegOrMem.interp_le hL rm s p hr

private theorem ShiftCountExpr.interp_le {L₁ L₂ : Labels} (hL : L₁.Le L₂)
    (c : ShiftCountExpr) (s : MachineData) (p : Std.Rco Int64)
    {r₁ r₂ : BitVec 8 → Effects} (hr : ∀ v, (r₁ v).Le (r₂ v)) :
    (@ShiftCountExpr.interp L₁ c s p r₁).Le (@ShiftCountExpr.interp L₂ c s p r₂) := by
  cases c with
  | cl => exact hr _
  | imm8 v => exact ConstExpr.interp_le hL v p fun _ => hr _

private theorem ShiftCountExpr.interpMasked_le {L₁ L₂ : Labels} (hL : L₁.Le L₂)
    (c : ShiftCountExpr) (s : MachineData) (p : Std.Rco Int64) (w : Width)
    {r₁ r₂ : Nat → Effects} (hr : ∀ v, (r₁ v).Le (r₂ v)) :
    (@ShiftCountExpr.interpMasked L₁ c s p w r₁).Le (@ShiftCountExpr.interpMasked L₂ c s p w r₂) :=
  ShiftCountExpr.interp_le hL c s p fun _ => hr _

private theorem RelRegOrMem.interp_le {L₁ L₂ : Labels} [AddressSize] (hL : L₁.Le L₂)
    (o : RelRegOrMem) (s : MachineData) (p : Std.Rco Int64)
    {r₁ r₂ : BitVec 64 → MachineData → Effects} (hr : ∀ v s', (r₁ v s').Le (r₂ v s')) :
    (@RelRegOrMem.interp L₁ _ o s p r₁).Le (@RelRegOrMem.interp L₂ _ o s p r₂) := by
  cases o with
  | rel c => exact ConstExpr.interp_le hL c p fun _ => hr _ _
  | reg _ => exact hr _ _
  | mem a => exact AddrExpr.interp_le hL a s.regs p fun _ => MachineData.load_le hr

private theorem ite_le {c : Prop} [Decidable c] {a₁ a₂ b₁ b₂ : Effects}
    (ha : a₁.Le a₂) (hb : b₁.Le b₂) :
    (if c then a₁ else b₁).Le (if c then a₂ else b₂) := by
  split <;> assumption

private theorem Operation.interp_le {L₁ L₂ : Labels} [AddressSize] {w : Width} (hL : L₁.Le L₂)
    (op : Operation w) (p : Std.Rco Int64) (s : MachineData)
    (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects) :
    (@Operation.interp L₁ _ w op p s next jmp).Le (@Operation.interp L₂ _ w op p s next jmp) := by
  cases op <;> dsimp only [Operation.interp, Reg.interp] <;>
    repeat (first
      | (with_reducible apply Operand.interp_le hL); intro _ _
      | (with_reducible apply RegOrMem.interp_le hL); intro _ _
      | (with_reducible apply AddrExpr.interp_le hL); intro _
      | (with_reducible apply ShiftCountExpr.interpMasked_le hL); intro _
      | (with_reducible apply RelRegOrMem.interp_le hL); intro _ _
      | (with_reducible apply MachineData.load_le); intro _ _
      | (with_reducible apply MachineData.set_le hL); intro _
      | (with_reducible apply Effects.Le.undefined_choice); intro _
      | (with_reducible apply label_le hL); intro _
      | (with_reducible apply ite_le)
      | exact Effects.Le.refl _)

private theorem AvxOperation.interp_le {L₁ L₂ : Labels} [AddressSize] {w : AvxWidth} (hL : L₁.Le L₂)
    (op : AvxOperation w) (p : Std.Rco Int64) (s : MachineData)
    (next : MachineData → Effects) :
    (@AvxOperation.interp L₁ _ w op p s next).Le (@AvxOperation.interp L₂ _ w op p s next) := by
  cases op <;> dsimp only [AvxOperation.interp] <;>
    repeat (first
      | (with_reducible apply AvxOperand.interp_le hL); intro _ _
      | (with_reducible apply AvxRegOrMem.interp_le hL); intro _ _
      | (with_reducible apply ConstExpr.interp_le hL); intro _
      | (with_reducible apply MachineData.setAvx_le hL); intro _
      | (with_reducible apply MachineData.setAvxLegacy_le hL); intro _
      | exact Effects.Le.refl _)

private theorem Directive.interp_le {L₁ L₂ : Labels} (hL : L₁.Le L₂)
    (d : Directive) (s : MachineData) (p : Std.Rco Int64)
    (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects) :
    (@Directive.interp L₁ d s p next jmp).Le (@Directive.interp L₂ d s p next jmp) := by
  match d with
  | .label _ => exact .refl _
  | .instr (.regular addr_sz _ op) =>
    letI : AddressSize := ⟨addr_sz⟩
    exact Effects.Le.require_exec (Operation.interp_le hL op p s next jmp)
  | .instr (.avx addr_sz _ op) =>
    letI : AddressSize := ⟨addr_sz⟩
    exact Effects.Le.require_exec (AvxOperation.interp_le hL op p s next)
  | .byteArray bs =>
    cases bs with | mk data =>
    cases data using Array.casesOn with
    | mk l => cases l <;> exact .refl _

theorem Directives.interp_mono_labels {L₁ L₂ : Labels} (hL : L₁.Le L₂)
    (ds : List (Kraken.Sized Directive)) (s : MachineData) (pc : Int64) (post : MachineState → Prop) :
    (@Directives.interp L₁ ds s pc).All post → (@Directives.interp L₂ ds s pc).All post := by
  induction ds generalizing s pc with
  | nil => exact id
  | cons d ds ih =>
    rcases d with ⟨d, sz⟩
    simp only [Directives.interp]
    intro h
    have h1 := Directive.interp_le hL d s ⟨pc, pc + .ofNat sz⟩ .next (fun a s' => .done ⟨s', a⟩)
      (fun s' => @Directives.interp L₁ ds s' (pc + .ofNat sz)) post h
    exact Effects.bind_mono _ (fun s' => ih s' (pc + .ofNat sz)) (fun _ => id) h1

private theorem labels_take_le {p₁ p₂ : Program} [l : Kraken.Layout (p₁ ++ p₂)] :
    letI := l.take p₁
    (Executable.labels p₁.toExecutable).Le (Executable.labels (p₁ ++ p₂).toExecutable) := by
  intro lbl a ha
  change (List.findSome? _ _) = some a at ha ⊢
  rw [Kraken.Program.toExecutable_append_withAddresses p₁ p₂, List.findSome?_append, ha]
  rfl

variable (p₁ p₂ : Program) [layout : Kraken.WellFormedLayout (p₁ ++ p₂)]
variable (zero_inert : ∀ i : Fin (p₁ ++ p₂).length, layout.size i = 0 → (p₁ ++ p₂)[i].Inert)

private theorem labels_drop_le :
    letI := layout.drop p₁
    (Executable.labels p₂.toExecutable).Le (Executable.labels (p₁ ++ p₂).toExecutable) := by
  intro lbl a ha
  let e₁ := (letI := layout.toLayout.take p₁; p₁.toExecutable)
  let e₂ := (letI := layout.toLayout.drop p₁; p₂.toExecutable)
  let f : Kraken.Addressable Directive → Option Int64 :=
    fun {directive, addr, ..} => if directive = .label lbl then .some addr else .none
  change List.findSome? f e₂.withAddresses = some a at ha
  change List.findSome? f (p₁ ++ p₂).toExecutable.withAddresses = some a
  have hmem₂ : lbl ∈ Kraken.Program.labels p₂ := by
    letI := layout.toLayout.drop p₁
    obtain ⟨⟨d, sz, addr⟩, hx, hfx⟩ := List.exists_of_findSome?_eq_some ha
    dsimp only [f] at hfx
    split at hfx
    · rename_i hd
      exact Kraken.Program.mem_labels_of_mem_withAddresses p₂ hx hd
    · contradiction
  have hnot₁ : lbl ∉ Kraken.Program.labels p₁ := by
    have hnodup : (Kraken.Program.labels p₁ ++ Kraken.Program.labels p₂).Nodup := by
      simpa [Kraken.Program.labels, List.filterMap_append] using layout.unique_labels
    intro hmem₁
    exact (List.nodup_append.mp hnodup).2.2 lbl hmem₁ lbl hmem₂ rfl
  have hnone₁ : List.findSome? f e₁.withAddresses = none := by
    letI := layout.toLayout.take p₁
    refine List.findSome?_eq_none_iff.mpr fun ⟨d, sz, addr⟩ hx => ?_
    dsimp only [f]
    split
    · rename_i hd
      exact absurd (Kraken.Program.mem_labels_of_mem_withAddresses p₁ hx hd) hnot₁
    · rfl
  have happ : (p₁ ++ p₂).toExecutable.withAddresses = e₁.withAddresses ++ e₂.withAddresses :=
    Kraken.Program.toExecutable_append_withAddresses p₁ p₂ (l := layout.toLayout)
  rw [happ, List.findSome?_append, hnone₁]
  exact ha

include zero_inert in
private theorem inert_of_mem_program
    {c : Kraken.Sized Directive} (hc : c ∈ (p₁ ++ p₂).toExecutable.program) (hz : c.size = 0) :
    Directive.Inert c.directive := by
  simp only [Kraken.Layout.apply, List.mem_iff_getElem] at hc
  obtain ⟨i, hi, heq⟩ := hc
  simp only [List.length_mapIdx] at hi
  simp only [List.getElem_mapIdx] at heq
  subst heq
  exact zero_inert ⟨i, hi⟩ hz

private theorem Eventually.lift_sub {e₁ e₂ : Executable}
    (hL : (Executable.labels e₁).Le (Executable.labels e₂))
    (hinert₁ : ∀ c ∈ e₁.program, c.size = 0 → Directive.Inert c.directive)
    (hat : ∀ pc, (∃ c ∈ e₁.directivesAtAddress pc, 0 < c.size) →
      ∃ pre, e₂.directivesAtAddress pc = pre ++ e₁.directivesAtAddress pc ∧
        ∀ c ∈ pre, c.size = 0 ∧ Directive.Inert c.directive)
    {post : MachineState → Prop} {init : MachineState}
    (h : Eventually (step1 e₁) post init) :
    Eventually (step1 e₂) post init := by
  induction h with
  | done s hp => exact .done s hp
  | step s mid_p hstep _ ih =>
    by_cases hpos : ∃ c ∈ e₁.directivesAtAddress s.pc, 0 < c.size
    · obtain ⟨pre, heq, hpre⟩ := hat s.pc hpos
      refine .step s mid_p ?_ ih
      dsimp only [step1, Executable.step] at hstep ⊢
      rw [heq]
      letI := Executable.labels e₂
      exact (Directives.interp_inert_append hpre s.data s.pc mid_p).mpr
        (Directives.interp_mono_labels hL (e₁.directivesAtAddress s.pc) s.data s.pc mid_p hstep)
    · have hall0 : ∀ c ∈ e₁.directivesAtAddress s.pc, c.size = 0 ∧ Directive.Inert c.directive := by
        intro c hc
        have hz : c.size = 0 := by
          rcases Nat.eq_zero_or_pos c.size with h0 | hp
          · exact h0
          · exact absurd ⟨c, hc, hp⟩ hpos
        exact ⟨hz, hinert₁ c (Kraken.Executable.mem_of_mem_directivesAtAddress hc) hz⟩
      dsimp only [step1, Executable.step] at hstep
      letI := Executable.labels e₁
      rw [← List.append_nil (e₁.directivesAtAddress s.pc),
          Directives.interp_inert_append hall0 s.data s.pc mid_p,
          Directives.interp, Effects.All] at hstep
      exact ih ⟨s.data, s.pc⟩ hstep

include zero_inert in
theorem Eventually.prepend
  (post : MachineState → Prop) (init : MachineState)
  (h : letI := layout.drop p₁
       Eventually (step1 p₂.toExecutable) post init) :
    Eventually (step1 (p₁ ++ p₂).toExecutable) post init :=
  Eventually.lift_sub
    (labels_drop_le p₁ p₂)
    (fun _ hc hz [Labels] => inert_of_mem_program p₁ p₂ zero_inert
      (Kraken.Program.toExecutable_append_program p₁ p₂ (l := layout.toLayout) ▸ List.mem_append_right _ hc) hz)
    (fun pc hpos => by
      obtain ⟨pre, heq, hpre⟩ := Kraken.Executable.directivesAtAddress_drop_eq p₁ p₂ pc hpos
      exact ⟨pre, heq, fun c hc =>
        let ⟨hmem, hz⟩ := hpre c hc
        ⟨hz, fun [Labels] => inert_of_mem_program p₁ p₂ zero_inert hmem hz⟩⟩)
    h

include zero_inert in
theorem Eventually.append
  (post : MachineState → Prop) (init : MachineState)
  (h : letI := layout.take p₁
       Eventually (step1 p₁.toExecutable) post init) :
    Eventually (step1 (p₁ ++ p₂).toExecutable) post init :=
  Eventually.lift_sub
    (labels_take_le (l := layout.toLayout))
    (fun _ hc hz [Labels] => inert_of_mem_program p₁ p₂ zero_inert
      (Kraken.Program.toExecutable_append_program p₁ p₂ (l := layout.toLayout) ▸ List.mem_append_left _ hc) hz)
    (fun pc hpos => ⟨[], by rw [List.nil_append]; exact Kraken.Executable.directivesAtAddress_take_eq p₁ p₂ pc hpos, by simp⟩)
    h
