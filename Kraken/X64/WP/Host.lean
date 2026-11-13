module

public import Kraken.Data.List.Infix
public import Kraken.X64.Inert
public import Kraken.X64.Semantics

/-!
# x86-64 Host Program Interface

Specializes `Host` projections and helper lemmas to x86-64 `Program` (`List Directive`).
-/

@[expose] public section

namespace Host

variable {p : Program} [h : Host p]

abbrev prog {p : Program} [Host p] : Program := p

@[instance_reducible]
def layout : Layout := Kraken.Host.layout (p := p)

abbrev exe : Executable := Kraken.Host.exe (p := p)

abbrev addrOf (k : Nat) : Int64 := Kraken.Host.addrOf (p := p) k

instance : Labels := Kraken.Host.labels (p := p)

theorem sizeBefore_eq_of_addrOf_eq {j k : Nat} (heq : Host.addrOf j = Host.addrOf k) :
    Host.exe.sizeBefore j = Host.exe.sizeBefore k :=
  Kraken.Host.sizeBefore_eq_of_addrOf_eq heq

theorem inert_of_getElem? {i : Nat} {d : Directive} (hd : Host.prog[i]? = some d)
    (hz : h.size i = 0) : Directive.Inert d :=
  Kraken.Host.inert_of_getElem? hd hz

abbrev startAddr {sub : Program} (hinf : sub.IsInfix Host.prog) : Int64 :=
  Kraken.Host.startAddr hinf

abbrev endAddr {sub : Program} (hinf : sub.IsInfix Host.prog) : Int64 :=
  Kraken.Host.endAddr hinf

theorem exe_getElem? (i : Nat) :
    Host.exe.program[i]? = Host.prog[i]?.map (fun d => {directive := d, size := h.size i}) :=
  Kraken.Host.exe_getElem? i

theorem addrOf_succ {k : Nat} {d : Directive} (hd : Host.prog[k]? = some d) :
    Host.addrOf (k + 1) = Host.addrOf k + .ofNat (h.size k) :=
  Kraken.Host.addrOf_succ hd

theorem inert_of_size_zero {d : Directive}
    (hmem : {directive := d, size := 0} ∈ Host.exe.program) : Directive.Inert d :=
  Kraken.Host.inert_of_size_zero hmem

theorem directivesAtAddress_addrOf {k : Nat} {c : Kraken.Sized Directive}
    (hc : Host.exe.program[k]? = some c) (hz : 0 < c.size) :
    ∃ pre, Host.exe.directivesAtAddress (Host.addrOf k) = pre ++ [c] ∧
      ∀ c ∈ pre, c.size = 0 :=
  Kraken.Host.directivesAtAddress_addrOf hc hz

theorem eventually_of_interp {k : Nat} {d : Directive} {sub : Program}
    (hdp : (d :: sub).IsInfixAt Host.prog k) {post : @Post MachineState} {s : MachineData}
    (hinterp : ((ArchDirective.interp d s ⟨Host.addrOf k, Host.addrOf (k + 1)⟩).onNext
      (fun s' => .done ⟨s', Host.addrOf (k + 1)⟩)
      (fun a s' => .done ⟨s', a⟩)).All (TracedPost.ofPost fun mid _ => post mid)) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩ :=
  Kraken.Host.eventually_of_interp hdp hinterp

end Host
