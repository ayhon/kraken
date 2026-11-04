module

import Kraken.Attribute

@[expose] public section

structure Effect.{u} where
  In : Type u
  Out : In → Type

namespace Effect

@[inline, kstep] abbrev mkNonrecoverable (In : Type _) : Effect :=  .mk In (fun _ => Empty)
@[inline, kstep] abbrev mkMark (In : Type _) : Effect :=  .mk In (fun _ => Unit)

@[kstep] def union.{u,v} (a : Effect.{u})(b : Effect.{v}) : Effect where
  In  := Sum     a.In  b.In
  Out := Sum.rec a.Out b.Out
infixl:30 " ∪ₑ "  => Effect.union

class Incl.{u,v} (a : Effect.{u})(b : Effect.{v}) where
  input : a.In → b.In
  proof : ∀ {x : a.In}, b.Out (input x) = a.Out x := by intros; rfl

attribute [match_pattern, kstep] Incl.input

@[inline, reducible, kstep] instance inclSelf.{u} (a : Effect.{u}) :
    a.Incl a where
  input x := x

@[inline, reducible, kstep] instance inclLeft.{u,v,w} (a : Effect.{u})(a' : Effect.{v})(b : Effect.{w}) [h : a.Incl a']:
    a.Incl (a' ∪ₑ b) where
  input x := .inl (Effect.Incl.input x)
  proof := h.proof.symm ▸ rfl

@[inline, reducible, kstep] instance inclRight.{u,v,w} (a : Effect.{u})(b : Effect.{v})(b' : Effect.{w}) [h : b.Incl b'] :
    b.Incl (a ∪ₑ b') where
  input x := .inr (Effect.Incl.input x)
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
@[kstep] def All : Trace eff Result → Prop
  | .fallthrough value => h.fpost value
  | .jump value => h.jpost value
  | .yield val cont =>
    h.epost val (cont · |>.All)

end Trace
