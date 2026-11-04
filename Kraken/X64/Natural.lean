module

public import Kraken.Natural
public import Kraken.X64.OmniSemantics

/-! # Factoring X64 `Directives.interp` through `Trace.bind` -/

public theorem X64Effects.All.epost_imp₂
    (val : X64Effects.All.In) {p₁ p₂ p : X64Effects.All.Out val → Prop}
    (hp : ∀ o, p₁ o → p₂ o → p o) :
    X64Effects.All.epost val p₁ →
    X64Effects.All.epost val p₂ →
    X64Effects.All.epost val p :=
  match val with
  | Effect.Incl.input (a := Unimplemented) _
  | Effect.Incl.input (a := GpUnaligned) _
  | Effect.Incl.input (a := NonMemLoad) _
  | Effect.Incl.input (a := NonMemStore) _ => fun h _ => h.elim
  | Effect.Incl.input (a := Undefined) ⟨_, _⟩ => fun h₁ h₂ o => hp o (h₁ o) (h₂ o)
  | Effect.Incl.input (a := RequireReadAccess) _
  | Effect.Incl.input (a := RequireWriteAccess) _
  | Effect.Incl.input (a := RequireExecAccess) _ => hp ()

section Bind
variable {k : Exit × MachineState → Effects}

theorem Effects.undefined_bind {β : Type} [NondetSupportingType β] (ret : β → Effects) :
    (Effects.undefined ret).bind k = Effects.undefined (fun v => (ret v).bind k) := rfl

theorem MachineData.load_bind (s : MachineData) (a : BitVec 64) (w : Width)
    (ret : w.type → MachineData → Effects) :
    (s.load a w ret).bind k = s.load a w (fun v s => (ret v s).bind k) := by
  unfold MachineData.load
  refine congrArg (require_read_access a w) (funext fun _ => ?_)
  split
  · rfl
  · exact congrArg (nonmem_load s.dmem a w) (funext fun (_, _) => rfl)

theorem MachineData.store_bind (s : MachineData) (a : BitVec 64) {w : Width} (v : w.type)
    (ret : MachineData → Effects) :
    (s.store a v ret).bind k = s.store a v (fun s => (ret s).bind k) := by
  unfold MachineData.store
  refine congrArg (require_write_access a w) (funext fun _ => ?_)
  split <;> rfl

theorem MachineData.storeAvx_bind (s : MachineData) (a : BitVec 64) {w : AvxWidth} (v : w.type)
    (ret : MachineData → Effects) (ca : Bool) :
    (s.storeAvx a v ret ca).bind k = s.storeAvx a v (fun s => (ret s).bind k) ca := by
  unfold MachineData.storeAvx
  split
  · exact Trace.yield_empty_bind
  · refine congrArg (require_write_access a .W64) (funext fun _ => ?_)
    split
    · rfl
    · exact Trace.yield_empty_bind

section
variable [Labels] [AddressSize]

theorem AvxRegOrMem.interp_bind {w} (o : AvxRegOrMem w) (s : MachineData) (p : Std.Rco Int64)
    (ret : w.type → MachineData → Effects) (ca : Bool) :
    (o.interp s p ret ca).bind k = o.interp s p (fun v s => (ret v s).bind k) ca := by
  cases o with
  | avx => rfl
  | mem =>
    simp only [AvxRegOrMem.interp]
    unfold MachineData.loadAvx
    split
    · exact Trace.yield_empty_bind
    · refine congrArg (require_read_access _ .W64) (funext fun _ => ?_)
      split
      · rfl
      · exact Trace.yield_empty_bind

theorem RegOrMem.interp_bind {w} (o : RegOrMem w) (s : MachineData) (p : Std.Rco Int64)
    (ret : w.type → MachineData → Effects) :
    (o.interp s p ret).bind k = o.interp s p (fun v s => (ret v s).bind k) := by
  cases o <;> simp only [RegOrMem.interp, MachineData.load_bind]

theorem Operand.interp_bind {w} (o : Operand w) (s : MachineData) (p : Std.Rco Int64)
    (ret : w.type → MachineData → Effects) :
    (o.interp s p ret).bind k = o.interp s p (fun v s => (ret v s).bind k) := by
  cases o <;> simp only [Operand.interp, RegOrMem.interp_bind]

theorem MachineData.set_bind {w} (d : Dst w) (v : w.type) (s : MachineData) (p : Std.Rco Int64)
    (ret : MachineData → Effects) :
    (s.set d v p ret).bind k = s.set d v p (fun s => (ret s).bind k) := by
  cases d <;> simp only [MachineData.set, MachineData.store_bind]

end

theorem Directives.interp_bind [Labels] (ds : List (Kraken.Sized Directive)) (s : MachineData)
    (pc : Int64) (ret jmp : Int64 → MachineData → Effects) :
    (Directives.interp ds s pc ret jmp).bind k =
      Directives.interp ds s pc (fun a s => (ret a s).bind k) (fun a s => (jmp a s).bind k) := by
  induction ds generalizing s pc with
  | nil => rfl
  | cons c ds ih =>
    obtain ⟨d, z⟩ := c
    unfold Directives.interp Directive.interp
    cases d with
    | label _ => exact ih _ _
    | byteArray _ => exact Trace.yield_empty_bind
    | instr i =>
      unfold Instr.interp
      refine congrArg (require_exec_access _) (funext fun _ => ?_)
      match i with
      | .regular asz w op =>
        letI : AddressSize := ⟨asz⟩
        cases op with
        | jmp tgt | call tgt =>
          cases tgt <;> simp only [Operation.interp, RelRegOrMem.interp,
            MachineData.load_bind, MachineData.store_bind]
        | _ =>
          simp only [Operation.interp, Reg.interp, apply_ite (Trace.bind · k),
            Operand.interp_bind, RegOrMem.interp_bind, MachineData.load_bind,
            MachineData.store_bind, MachineData.set_bind, Effects.undefined_bind, ih] <;>
            cases w <;> simp only [Effects.undefined_bind, ih]
      | .avx asz _ op =>
        letI : AddressSize := ⟨asz⟩
        cases op <;> rename_i dst _ <;> cases dst <;>
          simp only [AvxOperation.interp, AvxRegOrMem.interp_bind,
            MachineData.setAvx, MachineData.setAvxLegacy, MachineData.storeAvx_bind, ih]

end Bind

public theorem Directives.interp_eq_bind [Labels] (ds : List (Kraken.Sized Directive))
    (s : MachineData) (pc : Int64) (ret jmp : Int64 → MachineData → Effects) :
    Directives.interp ds s pc ret jmp =
      (Directives.interp ds s pc
          (fun a s => .fallthrough ⟨s, a⟩)
          (fun a s => .jump ⟨s, a⟩)).bind fun
        | (.fallthrough, st) => ret st.pc st.data
        | (.jump, st) => jmp st.pc st.data :=
  Eq.symm <| Directives.interp_bind ds s pc
    (fun a s => .fallthrough ⟨s, a⟩) (fun a s => .jump ⟨s, a⟩)

public theorem Directives.interp_ret_congr [Labels] (ds : List (Kraken.Sized Directive)) (s : MachineData)
    (pc : Int64) {ret ret' jmp : Int64 → MachineData → Effects}
    (h : ∀ s, ret (pc + .ofNat (ds.map (·.size)).sum) s = ret' (pc + .ofNat (ds.map (·.size)).sum) s) :
    Directives.interp ds s pc ret jmp = Directives.interp ds s pc ret' jmp := by
  induction ds generalizing s pc with
  | nil => simpa [Directives.interp] using h s
  | cons c ds ih =>
    obtain ⟨d, z⟩ := c
    simp only [Directives.interp]
    congr 1
    funext s'
    refine ih s' _ fun s => ?_
    simpa only [List.map_cons, List.sum_cons, Int64.ofNat_add, Int64.add_assoc] using h s
