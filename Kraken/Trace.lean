 module

public import Kraken.X64.Semantics

public section

structure Effect.{u} where
  In : Type u
  Out : In → Type

@[inline] abbrev Effect.mkNonrecoverable (In : Type _) : Effect :=  ⟨In, fun _ => Empty⟩
@[inline] abbrev Effect.mkMark (In : Type _) : Effect :=  ⟨In, fun _ => Unit⟩

@[expose]
def Effect.union.{u,v} (a : Effect.{u})(b : Effect.{v}) : Effect where
  In  := Sum     a.In  b.In
  Out := Sum.rec a.Out b.Out
infixl:30 " ∪ₑ "  => Effect.union

class Effect.Incl.{u,v} (a : Effect.{u})(b : Effect.{v}) where
  input : a.In → b.In
  proof : ∀ {x : a.In}, b.Out (input x) = a.Out x := by intros; rfl

@[inline, reducible] instance inclSelf.{u} (a : Effect.{u}) :
    a.Incl a where
  input := id

@[inline, reducible] instance inclLeft.{u,v,w} (a : Effect.{u})(a' : Effect.{v})(b : Effect.{w}) [h : a.Incl a']:
    a.Incl (a' ∪ₑ b) where
  input :=  Sum.inl ∘ Effect.Incl.input
  proof := h.proof.symm ▸ rfl

@[inline, reducible] instance inclRight.{u,v,w} (a : Effect.{u})(b : Effect.{v})(b' : Effect.{w}) [h : b.Incl b'] :
    b.Incl (a ∪ₑ b') where
  input := Sum.inr ∘ Effect.Incl.input
  proof := h.proof.symm ▸ rfl

variable (eff :  Effect) (Result : Type _) in
inductive Trace where
  | done (res : Result)
  | yield (value : eff.In) (cont : eff.Out value → Trace)

namespace Trace
variable {eff :  Effect} {Result : Type _}

def All (post : Result → Prop) : Trace eff Result → Prop
  | .done value => post value
  | .yield val cont =>
    Nonempty (eff.Out val) ∧  -- NOTE: We use `Nonempty` here to exclude traces without a result
    ∀ o, (cont o).All post

-- NOTE: Trans written like this is more of a predecessor relation.
variable (trans : (Trace eff Result → Prop) → (Trace eff Result → Prop)) in
variable (ret : (Trace eff Result → Prop)) in
-- NOTE: This definition is generic enough if we have some `o x`, `o x → o x` and ways to relate `x` with `o x`
-- Is there a mathematical structure with this shape?
inductive Eventually : Trace eff Result → Prop where
  | now {t} (h : ret t) : t.Eventually
  | later {t} (mid_p : Trace eff Result → Prop) (h : trans mid_p t /- t ∈ trans mid_p -/)
      (hn : ∀ y, mid_p y /- y ∈ mid_p -/ → y.Eventually) : t.Eventually

-- NOTE: This `Eventually` is not really defined for a trace. It is defined for a "transition system" such
-- as the one given by `trans` and `ret`. `ret` defines the final states, `trans` defines the transitions.

end Trace

-- Testing of semantics

namespace X64Effects

@[expose] def Unimplemented : Effect := Effect.mkNonrecoverable String
@[expose] def GpUnaligned : Effect := Effect.mkNonrecoverable <| BitVec 64 × Nat

@[expose] def NonMemLoad : Effect where
  In := DataMem × (BitVec 64) × Width
  Out := fun (_, _, w) => w.type × DataMem
@[expose] def NonMemStore : Effect where
  In := DataMem × (BitVec 64) × (w : Width) × w.type
  Out := fun _ => DataMem

@[expose] def Undefined : Effect where
  In := (α : Type) × NondetSupportingType α
  Out := fun ⟨α, _⟩ => α

@[expose] def RequireReadAccess : Effect := .mkMark <| BitVec 64 × Width
@[expose] def RequireWriteAccess : Effect := .mkMark <| BitVec 64 × Width
@[expose] def RequireExecAccess : Effect := .mkMark <| Std.Rco Int64

abbrev All := Unimplemented   ∪ₑ GpUnaligned
        ∪ₑ NonMemLoad         ∪ₑ NonMemStore
        ∪ₑ Undefined          ∪ₑ RequireReadAccess
        ∪ₑ RequireWriteAccess ∪ₑ RequireExecAccess

end X64Effects

abbrev Effects' := Trace X64Effects.All MachineState

namespace Effects'

@[match_pattern, expose] def unimplemented (msg : String) (fn : Empty → Effects' := nofun) : Effects' :=
  .yield (Effect.Incl.input (a := X64Effects.Unimplemented) msg) fn

@[match_pattern, expose] def gp_unaligned (addr : BitVec 64) (w : Nat) (fn : Empty → Effects' := nofun) : Effects' :=
  .yield (Effect.Incl.input (a := X64Effects.GpUnaligned) (addr, w)) fn

@[match_pattern, expose] def nonmem_load (dmem : DataMem) (addr : BitVec 64) (w : Width) (ret : w.type × DataMem → Effects') : Effects' :=
  .yield (Effect.Incl.input (a := X64Effects.NonMemLoad) (dmem, addr, w)) ret
@[match_pattern, expose] def nonmem_store (dmem : DataMem) (addr : BitVec 64) {w : Width} (v : w.type) (ret: DataMem → Effects') : Effects' :=
  .yield (Effect.Incl.input (a := X64Effects.NonMemStore) ⟨dmem, addr, w, v⟩) ret

@[match_pattern, expose] def undefined {α : Type} [ι : NondetSupportingType α] (ret : α → Effects') : Effects' :=
  .yield (Effect.Incl.input (a := X64Effects.Undefined) ⟨α, ι⟩) ret

@[match_pattern, expose] def require_read_access (addr : BitVec 64) (w : Width) (ok : Unit → Effects') : Effects' :=
  .yield (Effect.Incl.input (a := X64Effects.RequireReadAccess) ⟨addr, w⟩) ok
@[match_pattern, expose] def require_write_access (addr : BitVec 64) (w : Width) (ok : Unit → Effects') : Effects' :=
  .yield (Effect.Incl.input (a := X64Effects.RequireWriteAccess) ⟨addr, w⟩) ok
@[match_pattern, expose] def require_exec_access (p: Std.Rco Int64) (ok : Unit → Effects') : Effects' :=
  .yield (Effect.Incl.input (a := X64Effects.RequireExecAccess) p) ok

end Effects'

def Effects'.toEffects : Effects' → Effects
  | .done res => .done res
  | .unimplemented msg _ => .unimplemented msg
  | .gp_unaligned addr w _ => .gp_unaligned addr w
  | .nonmem_load dmem addr w ret => .nonmem_load dmem addr w (Effects'.toEffects <| ret ⟨·, ·⟩)
  | .nonmem_store dmem addr v ret => .nonmem_store dmem addr v (Effects'.toEffects <| ret ·)
  | .undefined (ι :=  _) ret => .undefined (Effects'.toEffects <| ret ·)
  | .require_read_access addr w ok => .require_read_access addr w (Effects'.toEffects <| ok ·)
  | .require_write_access addr w ok => .require_write_access addr w (Effects'.toEffects <| ok ·)
  | .require_exec_access p ok => .require_exec_access p (Effects'.toEffects <| ok ·)
