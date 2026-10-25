 module

public import Kraken.X64.Semantics

public section

structure Effect.{u} where
  In : Type u
  Out : In → Type

@[inline] abbrev Effect.mkFail (In : Type _) : Effect :=  ⟨In, fun _ => Empty⟩
@[inline] abbrev Effect.mkMark (In : Type _) : Effect :=  ⟨In, fun _ => Unit⟩

@[expose]
def Effect.union.{u,v} (a : Effect.{u})(b : Effect.{v}) : Effect where
  In  := Sum     a.In  b.In
  Out := Sum.rec a.Out b.Out
infixl:30 " ∪ₑ "  => Effect.union

class Effect.Incl.{u,v} (a : Effect.{u})(b : Effect.{v}) where
  input : a.In → b.In
  proof : ∀ {x : a.In}, b.Out (input x) = a.Out x := by intros; rfl

instance inclSelf.{u} (a : Effect.{u}) :
    a.Incl a where
  input := id

instance inclLeft.{u,v,w} (a : Effect.{u})(a' : Effect.{v})(b : Effect.{w}) [h : a.Incl a']:
    a.Incl (a' ∪ₑ b) where
  input :=  Sum.inl ∘ Effect.Incl.input
  proof := h.proof.symm ▸ rfl

instance inclRight.{u,v,w} (a : Effect.{u})(b : Effect.{v})(b' : Effect.{w}) [h : b.Incl b'] :
    b.Incl (a ∪ₑ b') where
  input := Sum.inr ∘ Effect.Incl.input
  proof := h.proof.symm ▸ rfl

variable (eff :  Effect) (Result : Type _) in
inductive Trace where
  | result (res : Result)
  | yield (value : eff.In) (cont : eff.Out value → Trace)

def Trace.mono {a b : Effect.{_}} {Result : Type _} [a.Incl b] : Trace a Result → Trace b Result
  | result res => .result res
  | yield v cont => .yield (Effect.Incl.input v) (Trace.mono <| cont <| Effect.Incl.proof.mp ·)

-- Testing of semantics

namespace X64Effects

abbrev Unimplemented : Effect := .mkFail String
abbrev GpUnaligned : Effect := .mkFail <| BitVec 64 × Nat

abbrev NonMemLoad : Effect where
  In := DataMem × (BitVec 64) × Width
  Out := fun (_, _, w) => w.type × DataMem
abbrev NonMemStore : Effect where
  In := DataMem × (BitVec 64) × (w : Width) × w.type
  Out := fun _ => DataMem

abbrev Undefined : Effect where
  In := (α : Type) × NondetSupportingType α
  Out := fun ⟨α, _⟩ => α

abbrev RequireReadAccess : Effect := .mkMark <| BitVec 64 × Width
abbrev RequireWriteAccess : Effect := .mkMark <| BitVec 64 × Width
abbrev RequireExecAccess : Effect := .mkMark <| Std.Rco Int64

abbrev All := Unimplemented   ∪ₑ GpUnaligned
        ∪ₑ NonMemLoad         ∪ₑ NonMemStore
        ∪ₑ Undefined          ∪ₑ RequireReadAccess
        ∪ₑ RequireWriteAccess ∪ₑ RequireExecAccess

end X64Effects

abbrev Effects' := Trace X64Effects.All MachineState

namespace Effects'


@[match_pattern, expose] def unimplemented (msg : String) : Effects' :=
  .mono (a := X64Effects.Unimplemented) (.yield msg nofun)

def gp_unaligned (addr : BitVec 64) (w : Nat) : Effects' :=
  .mono (a := X64Effects.GpUnaligned) (.yield (addr, w) nofun)

def nonmem_load (dmem : DataMem) (addr : BitVec 64) (w : Width) (ret : w.type → DataMem → Effects') : Effects' :=
  .mono (a := X64Effects.NonMemLoad) (.yield (dmem, addr, w) (fun (v, w) => ret v w))
def nonmem_store (dmem : DataMem) (addr : BitVec 64) {w : Width} (v : w.type) (ret: DataMem → Effects') : Effects' :=
  .mono (a := X64Effects.NonMemLoad) (.yield _ _)
def undefined {α : Type} [NondetSupportingType α] (ret : α → Effects') : Effects' :=
  .mono (a := X64Effects.Undefined) (.yield _ _)
def require_read_access (addr : BitVec 64) (w : Width) (ok : Unit → Effects') : Effects' :=
  .mono (a := X64Effects.RequireReadAccess) (.yield _ _)
def require_write_access (addr : BitVec 64) (w : Width) (ok : Unit → Effects') : Effects' :=
  .mono (a := X64Effects.RequireWriteAccess) (.yield _ _)
def require_exec_access (p: Std.Rco Int64) (ok : Unit → Effects') : Effects' :=
  .mono (a := X64Effects.RequireExecAccess) (.yield _ _)

end Effects'

def Effects'.toEffects : Effects' → Effects
  | .result res => .done res
