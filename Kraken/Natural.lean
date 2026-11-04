module

public import Kraken.Trace

/-! # Interaction of `Trace.All` with `Trace.bind` and conjunction -/

namespace Trace

public theorem yield_empty_bind {eff : Effect} {α : Type _}
    {val : eff.In} {fn : eff.Out val → Trace eff α} {k : α → Trace eff α}
    (h : eff.Out val = Empty := by rfl) :
    (Trace.yield val fn).bind k = .yield val fn :=
  congrArg (Trace.yield val) (funext fun o => nomatch h ▸ o)

@[simp] public theorem All_bind {eff : Effect} {α β : Type _}
    (epost : (val : eff.In) → (eff.Out val → Prop) → Prop)
    (post : β → Prop) (t : Trace eff α) (k : α → Trace eff β) :
    (t.bind k).All epost post ↔ t.All epost (fun a => (k a).All epost post) := by
  induction t with
  | done _ => rfl
  | yield val cont ih =>
    simp only [Trace.bind, All, funext fun o => propext (ih o)]

/-- Combining two `Trace.All` proofs on the same trace. -/
public theorem All.imp₂ {eff : Effect} {α : Type _}
    {epost₁ epost₂ epost : (val : eff.In) → (eff.Out val → Prop) → Prop}
    {post₁ post₂ post : α → Prop}
    (he : ∀ (val : eff.In) {p₁ p₂ p : eff.Out val → Prop},
      (∀ o, p₁ o → p₂ o → p o) → epost₁ val p₁ → epost₂ val p₂ → epost val p)
    (hp : ∀ a, post₁ a → post₂ a → post a)
    (t : Trace eff α) :
    t.All epost₁ post₁ → t.All epost₂ post₂ → t.All epost post := by
  induction t with
  | done a => exact hp a
  | yield val _ ih => exact he val ih

end Trace
