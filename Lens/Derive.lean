module

public import Lens.Frame
public meta import Lean

/-!
# Automatic Lens Generation (`make_lenses`) and Disjointness Automation (`lens_disjoint`)

Provides:
- `make_lenses StructName`: generates a `Lens` definition (`StructName.Lenses.<field>`) and its
  `LawfulLens` instance for every field of a non-recursive, non-dependent Lean `structure`
  (including polymorphic structures such as `MachineState MD`).
- `lens_disjoint`: tactic that automatically proves `Optic.Disjoint l₁ l₂` and
  `Optic.Independent l g` goals for structure field lenses, composed lenses, and derived views.
-/

public meta section

open Lean Meta Elab Command Tactic

namespace Optic.Derive

/-- Generate `StructName.Lenses.<field>` and its `LawfulLens` instance for every direct field of
`structName`. -/
elab "make_lenses " id:ident : command => liftTermElabM do
  let structName ← resolveGlobalConstNoOverload id
  let env ← getEnv
  let some structInfo := getStructureInfo? env structName
    | throwErrorAt id "`{structName}` is not a structure"
  let .inductInfo indInfo ← getConstInfo structName
    | throwErrorAt id "`{structName}` is not an inductive structure"
  if indInfo.isRec then
    throwErrorAt id "`make_lenses` does not support recursive structure `{structName}`"
  if indInfo.numIndices != 0 then
    throwErrorAt id "`make_lenses` does not support indexed structure `{structName}`"

  let ctorName := getStructureCtor env structName |>.name
  let levelParams := indInfo.levelParams
  let levelArgs := levelParams.map Level.param
  let ctorInfo ← getConstInfoCtor ctorName

  forallTelescopeReducing ctorInfo.type fun ctorArgs _ => do
    unless indInfo.numParams + structInfo.fieldNames.size == ctorArgs.size do
      throwErrorAt id "`make_lenses` requires `{structName}` to have non-inherited fields matching its constructor"

    let params := ctorArgs[:indInfo.numParams].toArray
    let fieldFVars := ctorArgs[indInfo.numParams:].toArray
    let fieldNames := structInfo.fieldNames
    let structTy := mkAppN (mkConst structName levelArgs) params

    for (fname, i) in fieldNames.zipIdx do
      let fty ← inferType fieldFVars[i]!
      if fty.hasAnyFVar (fun fv => fieldFVars.any (·.fvarId! == fv)) then
        throwErrorAt id "`make_lenses`: field `{fname}` of `{structName}` depends on earlier fields"
      let lensName := structName ++ `Lenses ++ fname
      let lawfulName := structName ++ `Lenses ++ (fname.appendAfter "_lawful")
      let lensVal ← withLocalDeclD `s structTy fun sVar => do
        let getFn ← mkLambdaFVars #[sVar] (mkProj structName i sVar)
        let setFn ← withLocalDeclD `v fty fun vVar => do
          let mut ctorCallArgs : Array Expr := params
          for j in [0:fieldNames.size] do
            if j == i then
              ctorCallArgs := ctorCallArgs.push vVar
            else
              ctorCallArgs := ctorCallArgs.push (mkProj structName j sVar)
          mkLambdaFVars #[sVar, vVar] (mkAppN (mkConst ctorName levelArgs) ctorCallArgs)
        let lensStruct ← mkAppM ``Optic.Lens.mk #[getFn, setFn]
        mkLambdaFVars params lensStruct
      let lensTy ← inferType lensVal
      addAndCompile <| Declaration.defnDecl {
        name := lensName
        levelParams := levelParams
        type := lensTy
        value := lensVal
        hints := .abbrev
        safety := .safe
      }
      setReducibleAttribute lensName

      -- Build LawfulLens instance
      let appliedLens := mkAppN (mkConst lensName levelArgs) params
      let lawfulTarget ← mkAppM ``Optic.LawfulLens #[appliedLens]
      let lawfulTy ← mkForallFVars params lawfulTarget
      let mvar ← mkFreshExprMVar lawfulTy
      let (_, g) ← mvar.mvarId!.introN params.size
      let [g1, g2, g3] ← g.constructor
        | throwError "make_lenses: failed to apply `LawfulLens.mk`"
      let closeByCasesRfl (goal : MVarId) (numIntros : Nat) : MetaM Unit := do
        let (xs, goal) ← goal.introN numIntros
        let subgoals ← goal.cases xs[0]!
        for sg in subgoals do
          sg.mvarId.refl
      closeByCasesRfl g1 2
      closeByCasesRfl g2 1
      closeByCasesRfl g3 3
      let lawfulVal ← instantiateMVars mvar
      addDecl <| Declaration.thmDecl {
        name := lawfulName
        levelParams := levelParams
        type := lawfulTy
        value := lawfulVal
      }
      addInstance lawfulName AttributeKind.global (eval_prio default)

/-- Discharge `Optic.Disjoint l₁ l₂`, `Optic.Independent l g`, or `Optic.Frame.Preserves` /
`Optic.Frame.Sub` goals on structure lenses, composed lenses, and derived getters by unfolding
and case-splitting on the source structure. -/
macro "lens_disjoint" : tactic =>
  `(tactic| (
    first
    | (rintro _ s ⟨v, h⟩; subst h; try cases s; rfl)
    | (intro s v₁ v₂; try cases s; rfl)
    | (intro s v; try cases s; rfl)
  ))

end Optic.Derive

end
