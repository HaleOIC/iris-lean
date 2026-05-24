module

public meta import Iris.ProofMode.Aesop.Rule.Commit.Basic
public meta import Iris.ProofMode.Tactics.HaveCore

public meta section

namespace Iris.ProofMode.Aesop.Rule.ApplyHyps

open Lean Meta Qq Std
open Iris.BI
open Iris.ProofMode

variable {Q : Type} [Queue Q]

private inductive ApplySource where
  | iris (hyp : IrisHyp) (intuitionistic : Bool)
  | lean (userName : Name) (fvarId : FVarId)

private structure ApplyHypExpansion where
  source : ApplySource
  goals : Array SubGoal
  fullContextIrisSubgoals : Array IrisGoal
  postState : SavedState

private def ApplySource.name : ApplySource → Name
  | .iris hyp .. => hyp.name
  | .lean userName .. => userName

private def ApplySource.usedHyp? : ApplySource → Option AppliedHyp
  | .iris hyp true => some (.intuitionistic hyp)
  | .iris hyp false => some (.spatial hyp)
  | .lean userName fvarId => some (.lean userName fvarId)

private partial def collectIntoWandPremises?
    {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)}
    (p : Q(Bool)) (hypType target : Q($prop)) :
    MetaM (Option (Array Expr)) := do
  let hypTypeExpr ← instantiateMVars hypType
  let targetExpr ← instantiateMVars target
  let some hypType ← checkTypeQ hypTypeExpr prop
    | throwError "iaesop: internal error: applyHyps hypothesis has wrong type"
  let some target ← checkTypeQ targetExpr prop
    | throwError "iaesop: internal error: applyHyps target has wrong type"
  let preState ← saveState
  let premise ← mkFreshExprMVarQ prop
  let premiseExpr : Expr := premise
  match ← ProofMode.trySynthInstanceQ
      q(IntoWand $p false $hypType .out $premise .in $target) with
  | .some _ => return some #[premiseExpr]
  | .none | .undef => restoreState preState
  let preState ← saveState
  let premise ← mkFreshExprMVarQ prop
  let premiseExpr : Expr := premise
  let restTarget ← mkFreshExprMVarQ prop
  match ← ProofMode.trySynthInstanceQ
      q(IntoWand $p false $hypType .out $premise .out $restTarget) with
  | .none | .undef =>
    restoreState preState
    return none
  | .some _ =>
    match ← collectIntoWandPremises? (bi := bi) q(false) restTarget target with
    | some premises => return some (#[premiseExpr] ++ premises)
    | none =>
      restoreState preState
      return none

private def mkChildren
    (irisGoal : IrisGoal) (tag : Name)
    {e' : Q($irisGoal.prop)} (hyps' : Hyps irisGoal.bi e')
    (premises : Array Expr) : MetaM (Array SubGoal × Array IrisGoal) := do
  let mut goals : Array SubGoal := #[]
  let mut irisSubgoals : Array IrisGoal := #[]
  for premiseExpr in premises do
    let premiseExpr ← instantiateMVars premiseExpr
    let some premise ← checkTypeQ premiseExpr irisGoal.prop
      | throwError "iaesop: internal error: applyHyps premise has wrong type"
    let childIrisGoal := {
      irisGoal with
      e := e'
      hyps := hyps'
      goal := premise
    }
    let goalExpr ← mkFreshExprSyntheticOpaqueMVar (IrisGoal.toExpr childIrisGoal) tag
    let goal := goalExpr.mvarId!
    goals := goals.push {
      goal
      addedFVars := {}
      removedFVars := {}
    }
    irisSubgoals := irisSubgoals.push childIrisGoal
  return (goals, irisSubgoals)

private def mkIrisApplyHypExpansion?
    {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)}
    (irisGoal : IrisGoal) (target : Q($prop)) (tag : Name)
    (name : Name) (ivar : IVarId) (p : Q(Bool)) (ty : Q($prop)) :
    MetaM (Option ApplyHypExpansion) := do
  let some premises ← collectIntoWandPremises? (bi := bi) p ty target
    | return none
  if premises.isEmpty then
    return none
  let some ⟨_, _, hyps', _, _, _, _, _⟩ ←
      irisGoal.hyps.removeG true fun _ ivar' _ _ => do
        if ivar == ivar' then return some ()
        else return none
    | throwError "iaesop: internal error: applyHyps candidate disappeared"
  let (goals, fullContextIrisSubgoals) ←
    mkChildren irisGoal tag hyps' premises
  return some {
    source := .iris { name, ivar } (isTrue p)
    goals
    fullContextIrisSubgoals
    postState := ← saveState
  }

private def mkLeanApplyHypExpansion?
    (irisGoal : IrisGoal) (targetExpr : Expr) (tag : Name)
    (decl : LocalDecl) : MetaM (Option ApplyHypExpansion) := do
  let { prop, bi, .. } := irisGoal
  let targetExpr ← instantiateMVars targetExpr
  let some target ← checkTypeQ targetExpr prop
    | throwError "iaesop: internal error: applyHyps target has wrong type"
  let val := mkFVar decl.fvarId
  let ty ← instantiateMVars (← inferType val)
  let ⟨newMVars, _, _⟩ ← forallMetaTelescope ty
  let val := mkAppN val newMVars
  let ty ← instantiateMVars (← inferType val)
  if ! (← Meta.isProp ty) then
    return none
  have ty : Q(Prop) := ty
  let hyp ← mkFreshExprMVarQ prop
  match ← ProofMode.trySynthInstanceQ
      q(AsEmpValid .into $ty .in $prop .in $bi $hyp) with
  | .none | .undef =>
    return none
  | .some _ =>
    let some premises ← collectIntoWandPremises? (bi := bi) q(true) hyp target
      | return none
    if premises.isEmpty then
      return none
    let (goals, fullContextIrisSubgoals) ←
      mkChildren irisGoal tag irisGoal.hyps premises
    return some {
      source := .lean decl.userName decl.fvarId
      goals
      fullContextIrisSubgoals
      postState := ← saveState
    }

private partial def collectIrisApplyHypExpansions
    {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)}
    (irisGoal : IrisGoal) (target : Q($prop)) (tag : Name)
    (baseState : SavedState) :
    ∀ {e}, Hyps bi e → MetaM (Array ApplyHypExpansion)
  | _, .emp _ => return #[]
  | _, .hyp _ name ivar p ty _ => do
    restoreState baseState
    let expansion? ←
      mkIrisApplyHypExpansion? (bi := bi) irisGoal target tag name ivar p ty
    restoreState baseState
    return expansion?.toArray
  | _, .sep _ _ _ _ lhs rhs => do
    return (← collectIrisApplyHypExpansions irisGoal target tag baseState lhs) ++
      (← collectIrisApplyHypExpansions irisGoal target tag baseState rhs)

private def collectLeanApplyHypExpansions
    (irisGoal : IrisGoal) (targetExpr : Expr) (tag : Name)
    (baseState : SavedState) : MetaM (Array ApplyHypExpansion) := do
  let mut expansions := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then
      continue
    restoreState baseState
    if let some expansion ← mkLeanApplyHypExpansion? irisGoal targetExpr tag decl then
      expansions := expansions.push expansion
  restoreState baseState
  return expansions

private def mkApplyHypExpansions (goal : MVarId) :
    MetaM (Option (Array ApplyHypExpansion)) := do
  goal.withContext do
    let goalType ← instantiateMVars (← goal.getType)
    let some irisGoal := parseIrisGoal? goalType
      | return none
    let targetExpr ← instantiateMVars irisGoal.goal
    let some target ← checkTypeQ targetExpr irisGoal.prop
      | throwError "iaesop: internal error: applyHyps target has wrong type"
    let tag ← goal.getTag
    let baseState ← saveState
    let irisExpansions ←
      collectIrisApplyHypExpansions irisGoal target tag baseState irisGoal.hyps
    restoreState baseState
    let leanExpansions ←
      collectLeanApplyHypExpansions irisGoal targetExpr tag baseState
    let expansions := irisExpansions ++ leanExpansions
    if expansions.isEmpty then
      return none
    return some expansions

def run (input : RuleInput) : SearchM Q RuleOutput := do
  let goal := input.goal
  let some expansions ← liftM do
      restoreState input.state
      mkApplyHypExpansions goal
    | return {}
  let specs ← expansions.mapM λ expansion => do
    dbg_trace s!"applyHyps selected {expansion.source.name} and generated {expansion.goals.size} goals"
    for irisGoal in expansion.fullContextIrisSubgoals do
      let targetFmt ← liftM <| ppExpr irisGoal.goal
      dbg_trace s!"  applyHyps child target: {targetFmt.pretty}"
    return {
      goals := expansion.goals
      postState := expansion.postState
      successPossibility := .hundred
      effect := some (.contextManagement
        expansion.fullContextIrisSubgoals expansion.source.usedHyp?)
    }
  return RuleOutput.ofRappSpecs specs

def replay (input : RuleReplayInput) : ProofModeM (Array MVarId) := do
  return #[input.goal]

end Iris.ProofMode.Aesop.Rule.ApplyHyps
