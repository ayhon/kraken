module

public import Kraken.X64.Semantics
public import Std.WP
public import Kraken.X64.OmniSemantics

public section

structure Effect.{u} where
  In : Type u
  Out : In → Type

namespace Effect

@[inline] abbrev mkNonrecoverable (In : Type _) : Effect :=  .mk In (fun _ => Empty)
@[inline] abbrev mkMark (In : Type _) : Effect :=  .mk In (fun _ => Unit)

@[expose]
def union.{u,v} (a : Effect.{u})(b : Effect.{v}) : Effect where
  In  := Sum     a.In  b.In
  Out := Sum.rec a.Out b.Out
infixl:30 " ∪ₑ "  => Effect.union

class Incl.{u,v} (a : Effect.{u})(b : Effect.{v}) where
  input : a.In → b.In
  proof : ∀ {x : a.In}, b.Out (input x) = a.Out x := by intros; rfl

attribute [match_pattern] Incl.input

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

end Effect

variable (eff :  Effect) (Result : Type _) in
inductive Trace where
  | fallthrough (res : Result)
  | jump (res : Result)
  | yield (value : eff.In) (cont : eff.Out value → Trace)

namespace Trace
variable {eff :  Effect} {Result : Type _}

structure All.Handlers (eff : Effect) (Result : Type _) where
  post  : Result → Prop
  jpost : Result → Prop := post
  fpost : Result → Prop := post
  epost : (val : eff.In) → (eff.Out val → Prop) → Prop :=
    λ _ contP => ∀ x, contP x

-- variable (wp : Label → MachineState → (MachineState → Prop) → Prop) in
variable (h : All.Handlers eff Result)
def All : Trace eff Result → Prop
  | .fallthrough value => h.fpost value
  | .jump value => h.jpost value
  | .yield val cont =>
    h.epost val (cont · |>.All)

end Trace

-- Testing of semantics

-- namespace X64Effects

-- @[expose] def Unimplemented : Effect := Effect.mkNonrecoverable String
-- @[expose] def GpUnaligned : Effect := Effect.mkNonrecoverable <| BitVec 64 × Nat

-- @[expose] def NonMemLoad : Effect where
--   In := DataMem × (BitVec 64) × Width
--   Out := fun (_, _, w) => w.type × DataMem
-- @[expose] def NonMemStore : Effect where
--   In := DataMem × (BitVec 64) × (w : Width) × w.type
--   Out := fun _ => DataMem

-- @[expose] def Undefined : Effect where
--   In := (α : Type) × NondetSupportingType α
--   Out := fun ⟨α, _⟩ => α

-- @[expose] def RequireReadAccess : Effect := .mkMark <| BitVec 64 × Width
-- @[expose] def RequireWriteAccess : Effect := .mkMark <| BitVec 64 × Width
-- @[expose] def RequireExecAccess : Effect := .mkMark <| Std.Rco Int64

-- abbrev All := Unimplemented   ∪ₑ GpUnaligned
--         ∪ₑ NonMemLoad         ∪ₑ NonMemStore
--         ∪ₑ Undefined          ∪ₑ RequireReadAccess
--         ∪ₑ RequireWriteAccess ∪ₑ RequireExecAccess

-- def All.isError : All.In → Bool
--   | Effect.Incl.input (a := Unimplemented) _
--   | Effect.Incl.input (a := GpUnaligned) _
--   | Effect.Incl.input (a := NonMemLoad) _
--   | Effect.Incl.input (a := NonMemStore) _
--     => true
--   | Effect.Incl.input (a := Undefined) _
--   | Effect.Incl.input (a := RequireReadAccess) _
--   | Effect.Incl.input (a := RequireWriteAccess) _
--   | Effect.Incl.input (a := RequireExecAccess) _
--     => false

-- def All.Handlers (post : MachineState → Prop) : Trace.All.Handlers _ _ where
--   post := post
--   epost val contP := ¬ All.isError val ∧ ∀ o, contP o

-- end X64Effects

-- abbrev Effects' := Trace X64Effects.All MachineState

-- namespace Effects'

-- @[match_pattern, expose] def unimplemented (msg : String) (fn : Empty → Effects' := nofun) : Effects' :=
--   .yield (Effect.Incl.input (a := X64Effects.Unimplemented) msg) fn

-- @[match_pattern, expose] def gp_unaligned (addr : BitVec 64) (w : Nat) (fn : Empty → Effects' := nofun) : Effects' :=
--   .yield (Effect.Incl.input (a := X64Effects.GpUnaligned) (addr, w)) fn

-- @[match_pattern, expose] def nonmem_load (dmem : DataMem) (addr : BitVec 64) (w : Width) (ret : w.type × DataMem → Effects') : Effects' :=
--   .yield (Effect.Incl.input (a := X64Effects.NonMemLoad) (dmem, addr, w)) ret
-- @[match_pattern, expose] def nonmem_store (dmem : DataMem) (addr : BitVec 64) {w : Width} (v : w.type) (ret: DataMem → Effects') : Effects' :=
--   .yield (Effect.Incl.input (a := X64Effects.NonMemStore) ⟨dmem, addr, w, v⟩) ret

-- @[match_pattern, expose] def undefined {α : Type} [ι : NondetSupportingType α] (ret : α → Effects') : Effects' :=
--   .yield (Effect.Incl.input (a := X64Effects.Undefined) ⟨α, ι⟩) ret

-- @[match_pattern, expose] def require_read_access (addr : BitVec 64) (w : Width) (ok : Unit → Effects') : Effects' :=
--   .yield (Effect.Incl.input (a := X64Effects.RequireReadAccess) ⟨addr, w⟩) ok
-- @[match_pattern, expose] def require_write_access (addr : BitVec 64) (w : Width) (ok : Unit → Effects') : Effects' :=
--   .yield (Effect.Incl.input (a := X64Effects.RequireWriteAccess) ⟨addr, w⟩) ok
-- @[match_pattern, expose] def require_exec_access (p: Std.Rco Int64) (ok : Unit → Effects') : Effects' :=
--   .yield (Effect.Incl.input (a := X64Effects.RequireExecAccess) p) ok

-- end Effects'
