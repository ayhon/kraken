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

variable (eff : Effect) (Result : Type _) in
inductive Trace where
  | done (res : Result)
  | yield (value : eff.In) (cont : eff.Out value → Trace)

namespace Trace

@[kstep] protected def map.{u, v, w} {eff : Effect.{u}} {α : Type v} {β : Type w}
    (f : α → β) : Trace eff α → Trace eff β
  | .done a => .done (f a)
  | .yield val cont => .yield val (fun o => Trace.map f (cont o))

@[kstep] protected def bind.{u, v, w} {eff : Effect.{u}} {α : Type v} {β : Type w}
    (t : Trace eff α) (f : α → Trace eff β) : Trace eff β :=
  match t with
  | .done a => f a
  | .yield val cont => .yield val (fun o => Trace.bind (cont o) f)

instance instMonad.{u, v} {eff : Effect.{u}} : Monad (Trace.{u, v} eff) where
  pure := .done
  map := Trace.map
  bind := Trace.bind

instance instLawfulMonad.{u, v} {eff : Effect.{u}} : LawfulMonad (Trace.{u, v} eff) :=
  LawfulMonad.mk'
    (id_map := fun t => by
      induction t with
      | done _ => rfl
      | yield _ _ ih => exact congrArg _ (funext ih))
    (pure_bind := fun _ _ => rfl)
    (bind_assoc := fun t _ _ => by
      induction t with
      | done _ => rfl
      | yield _ _ ih => exact congrArg _ (funext ih))
    (bind_pure_comp := fun _ t => by
      induction t with
      | done _ => rfl
      | yield _ _ ih => exact congrArg _ (funext ih))

@[kstep] def All {eff : Effect} {Result : Type _}
    (epost : (val : eff.In) → (eff.Out val → Prop) → Prop)
    (post : Result → Prop) : Trace eff Result → Prop
  | .done value => post value
  | .yield val cont => epost val (fun o => All epost post (cont o))

end Trace
