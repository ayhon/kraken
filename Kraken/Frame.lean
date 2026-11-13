module

public meta import Lean

/-!
# Register Frames (`≡ … except` and `≡ … on`)

A block specification states which registers a block *writes*; every other register is
preserved. `r' ≡ r except [X13, X14]` says that register files `r'` and `r` agree on every
register other than `X13` and `X14`. The register names are resolved against the `RegFile`
instance of the register-file type, so the notation (and the tactics `kframe`/`kframe_eqs`)
work for any architecture.
-/

@[expose] public section

namespace Kraken

/-! ### Register Files and Frame Relations -/

/-- A register file `R` with a finite set of register `Name`s, all holding 64-bit values. -/
class RegFile (R : Type) where
  Name : Type
  get : R → Name → UInt64
  /-- All register names. -/
  names : List Name
  mem_names : ∀ n, n ∈ names

namespace RegFile

variable {R : Type} [RegFile R]

/-- `r'` agrees with `r` on every register not in `W`. -/
def EqExcept (W : List (Name R)) (r' r : R) : Prop :=
  ∀ n, n ∉ W → RegFile.get r' n = RegFile.get r n

theorem EqExcept.refl (W : List (Name R)) (r : R) : EqExcept W r r :=
  fun _ _ => rfl

theorem EqExcept.get {W : List (Name R)} {r' r : R} (h : EqExcept W r' r)
    (n : Name R) (hn : n ∉ W := by simp) : RegFile.get r' n = RegFile.get r n :=
  h n hn

theorem EqExcept.mono {W W' : List (Name R)} {r' r : R} (h : EqExcept W r' r)
    (hW : ∀ n, n ∈ W → n ∈ W') : EqExcept W' r' r :=
  fun n hn => h n fun hmem => hn (hW n hmem)

theorem EqExcept.trans {W₁ W₂ : List (Name R)} {r₁ r₂ r₃ : R}
    (h₁ : EqExcept W₁ r₂ r₁) (h₂ : EqExcept W₂ r₃ r₂) : EqExcept (W₁ ++ W₂) r₃ r₁ :=
  fun n hn =>
    have hn₁ : n ∉ W₁ := fun h => hn (List.mem_append_left _ h)
    have hn₂ : n ∉ W₂ := fun h => hn (List.mem_append_right _ h)
    (h₂ n hn₂).trans (h₁ n hn₁)

theorem EqExcept.symm {W : List (Name R)} {r' r : R} (h : EqExcept W r' r) : EqExcept W r r' :=
  fun n hn => (h n hn).symm

theorem EqExcept.nil_iff {r' r : R} : EqExcept [] r' r ↔ ∀ n, RegFile.get r' n = RegFile.get r n :=
  ⟨fun h n => h n (List.not_mem_nil), fun h n _ => h n⟩

/-- A register-file projection or derived view `proj : R → α`. -/
structure View (R : Type) where
  {α : Type}
  proj : R → α

def View.of {R α : Type} (f : R → α) : View R := ⟨f⟩

/-- `r'` agrees with `r` on every register or view in `vs`. -/
def EqOn {R : Type} (vs : List (View R)) (r' r : R) : Prop :=
  ∀ v ∈ vs, v.proj r' = v.proj r

theorem EqOn.refl {R : Type} (vs : List (View R)) (r : R) : EqOn vs r r :=
  fun _ _ => rfl

theorem EqOn.nil {R : Type} (r' r : R) : EqOn ([] : List (View R)) r' r :=
  fun _ h => nomatch h

theorem EqOn.cons {R : Type} {v : View R} {vs : List (View R)} {r' r : R}
    (h : v.proj r' = v.proj r) (hs : EqOn vs r' r) : EqOn (v :: vs) r' r := by
  intro w hw
  cases hw with
  | head => exact h
  | tail _ hw' => exact hs w hw'

end RegFile

end Kraken

end

public meta section

open Lean Meta Elab Term

namespace Kraken.RegFile

/-! ### Syntax and Elaboration for `≡ … except` and `≡ … on` -/

/-- `r' ≡ r except [a, b, …]`: `r'` and `r` agree on all registers but `a, b, …`
(see `Kraken.RegFile.EqExcept`). Each entry may be a constructor of the register-name type of
`r'`/`r` (possibly nested one level, e.g. `X13` for `XRegOrSp.reg XReg.X13`) or a derived view
`f : R → α` (e.g. a tuple view `fun r => (r.X3, r.X4)`, which expands to the registers `[X3, X4]`
it reads). -/
syntax:50 term:51 " ≡ " term:51 " except " "[" ident,* "]" : term

/-- `r' ≡ r on [a, b, …]`: `r'` and `r` agree on the listed registers or derived views
(e.g. `SP`, `X29`, or a custom projection `f : R → α`; see `Kraken.RegFile.EqOn`). Each name is
resolved on the register-file type `R` first (`R.<name>`), or elaborated directly as a function
`R → α`. -/
syntax:50 term:51 " ≡ " term:51 " on " "[" ident,* "]" : term

/-- Resolve a register name against the constructors of `nameTy` (one level of nesting allowed). -/
private def resolveRegName? (nameTy : Lean.Name) (id : Ident) : MetaM (Option Expr) := do
  let s := id.getId.toString
  let info ← getConstInfoInduct nameTy
  for c in info.ctors do
    let cinfo ← getConstInfoCtor c
    if c.getString! == s && cinfo.numFields == 0 then
      return some (mkConst c)
  for c in info.ctors do
    let cinfo ← getConstInfoCtor c
    if cinfo.numFields == 1 then
      let fieldTy ← forallTelescopeReducing cinfo.type fun xs _ => do
        inferType xs[xs.size - 1]!
      if let .const innerTy _ := fieldTy.getAppFn then
        if let some innerInfo := (← getEnv).find? innerTy then
          if let .inductInfo innerInd := innerInfo then
            for c' in innerInd.ctors do
              let c'info ← getConstInfoCtor c'
              if c'.getString! == s && c'info.numFields == 0 then
                return some (mkApp (mkConst c) (mkConst c'))
  return none

/-- Resolve a register projection or derived view `id` on register-file type `R` into `View.of f`. -/
private def resolveView (R : Expr) (id : Ident) : TermElabM Expr := do
  let mut cands : Array Ident := #[]
  if let .const RName _ := R.getAppFn then
    cands := cands.push (mkIdentFrom id (RName ++ id.getId))
    cands := cands.push (mkIdentFrom id (Lean.Name.mkSimple RName.getString! ++ id.getId))
  cands := cands.push id
  for cand in cands do
    let s ← saveState
    try
      let α ← mkFreshTypeMVar
      let expectedTy ← mkArrow R α
      let f ← withoutErrToSorry <| elabTermEnsuringType cand expectedTy
      Term.synthesizeSyntheticMVarsNoPostponing
      return ← mkAppM ``Kraken.RegFile.View.of #[f]
    catch _ =>
      s.restore
  throwErrorAt id "unknown register or view `{id.getId}` on `{R}`"

/-- Unroll a literal list expression into its elements. -/
private partial def literalListElems (l : Expr) : MetaM (Array Expr) := do
  let mut acc := #[]
  let mut cur ← whnfD l
  while cur.isAppOfArity ``List.cons 3 do
    acc := acc.push (cur.getArg! 1)
    cur ← whnfD (cur.getArg! 2)
  return acc

/-- Resolve an entry of `≡ … except […]` / `(writes := […])` to one or more register names:
either a single register constructor of `nameTy`, or the registers read by a view `f : R → α`. -/
private def resolveRegOrViewNames (R inst : Expr) (nameTy : Lean.Name) (id : Ident) :
    TermElabM (Array Expr) := do
  if let some reg ← (resolveRegName? nameTy id : MetaM (Option Expr)) then
    return #[reg]
  let v ← resolveView R id
  let f := v.getArg! 2
  let names ← literalListElems (mkApp2 (mkConst ``Kraken.RegFile.names) R inst)
  withLocalDeclD `r R fun rVar => do
    let body ← Meta.transform (mkApp f rVar) (pre := fun e => do
      let e := e.headBeta
      if e.getAppArgs.contains rVar then
        if let some e' ← unfoldDefinition? e then
          return .visit e'.headBeta
      return .continue)
    let mut regs := #[]
    for n in names do
      let projRaw ← whnfD (mkApp4 (mkConst ``Kraken.RegFile.get) R inst rVar n)
      if (body.find? (· == projRaw)).isSome then
        regs := regs.push n
    if regs.isEmpty then
      throwErrorAt id "view `{id.getId}` does not read any registers of `{R}`"
    return regs

elab_rules : term
  | `($r':term ≡ $r:term except [$ns:ident,*]) => do
    let r' ← elabTerm r' none
    let R ← instantiateMVars (← inferType r')
    let r ← elabTermEnsuringType r R
    let inst ← synthInstance (mkApp (mkConst ``Kraken.RegFile) R)
    let nameTyE ← whnf (mkApp2 (mkConst ``Kraken.RegFile.Name) R inst)
    let .const nameTy _ := nameTyE.getAppFn
      | throwError "`≡ … except` : register names of `{R}` are not an inductive type ({nameTyE})"
    let elemGroups ← ns.getElems.mapM fun id => resolveRegOrViewNames R inst nameTy id
    let mut elems : Array Expr := #[]
    for grp in elemGroups do
      for reg in grp do
        unless elems.contains reg do
          elems := elems.push reg
    let W ← mkListLit nameTyE elems.toList
    return mkAppN (mkConst ``Kraken.RegFile.EqExcept) #[R, inst, W, r', r]
  | `($r':term ≡ $r:term on [$ns:ident,*]) => do
    let r' ← elabTerm r' none
    let R ← instantiateMVars (← inferType r')
    let r ← elabTermEnsuringType r R
    let elems ← ns.getElems.mapM fun id => resolveView R id
    let viewTy := mkApp (mkConst ``Kraken.RegFile.View) R
    let vs ← mkListLit viewTy elems.toList
    return mkAppN (mkConst ``Kraken.RegFile.EqOn) #[R, vs, r', r]

/-- Last identifier component of a register-name term, for pretty printing. -/
private partial def regNameIdent? (stx : Term) : Option Ident :=
  match stx with
  | `(↑$a:term) => regNameIdent? a
  | `($f:ident $a:term) => regNameIdent? a <|> some (mkIdent f.getId.getString!.toName)
  | `($x:ident) => some (mkIdent x.getId.getString!.toName)
  | `(.$x:ident) => some x
  | `(.$f:ident $a:term) => regNameIdent? a <|> some f
  | `(($t:term)) => regNameIdent? t
  | _ => none

@[app_unexpander Kraken.RegFile.EqExcept]
def unexpandEqExcept : PrettyPrinter.Unexpander
  | `($_ [$ns:term,*] $r' $r) => do
    let some ids := ns.getElems.mapM regNameIdent? | throw ()
    `($r' ≡ $r except [$ids,*])
  | _ => throw ()

@[app_unexpander Kraken.RegFile.EqOn]
def unexpandEqOn : PrettyPrinter.Unexpander
  | `($_ [$vs:term,*] $r' $r) => do
    let some ids := vs.getElems.mapM regNameIdent? | throw ()
    `($r' ≡ $r on [$ids,*])
  | _ => throw ()

end Kraken.RegFile

end
