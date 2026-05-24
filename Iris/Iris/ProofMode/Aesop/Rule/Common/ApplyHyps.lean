module

public meta import Iris.ProofMode.Aesop.Rule.Commit.Basic
public meta import Iris.ProofMode.Tactics.Assumption
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
  match ← ProofMode.trySynthInstanceQ q(FromAssumption $p .in $hypType $target) with
  | .some _ => return some #[]
  | .none | .undef => restoreState preState
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

private def mkChildren (irisGoal : IrisGoal) (tag : Name)
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

/- Collect apply expansions from Iris local hypotheses. -/
private partial def collectFromIris
    {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)}
    (irisGoal : IrisGoal) (tag : Name) (baseState : SavedState) :
    ∀ {e}, Hyps bi e → MetaM (Array ApplyHypExpansion)
  | _, .emp _ => return #[]
  | _, .sep _ _ _ _ lhs rhs => do
    return (← collectFromIris irisGoal tag baseState lhs) ++
      (← collectFromIris irisGoal tag baseState rhs)
  | _, .hyp _ name ivar p ty _ => do
    baseState.restore
    let some premises ← collectIntoWandPremises? (bi := bi) p ty irisGoal.goal
      | return #[]
    let some ⟨_, _, hyps', _, _, _, _, _⟩ ←
        irisGoal.hyps.removeG false λ _ ivar' _ _ => do
          if ivar == ivar' then return some ()
          else return none
      | throwError "iaesop: applyHyps candidate disappear from Hyps"
    let (goals, fullContextIrisSubgoals) ← mkChildren irisGoal tag hyps' premises
    let expansion : ApplyHypExpansion := {
      source := .iris { name, ivar } (isTrue p)
      goals
      fullContextIrisSubgoals
      postState := ← saveState
    }
    baseState.restore
    return #[expansion]

/- Collect apply expansions from Lean local hypotheses. -/
private def collectFromLean (irisGoal : IrisGoal) (tag : Name)
    (baseState : SavedState) : MetaM (Array ApplyHypExpansion) := do
  let { prop, bi, goal := target, .. } := irisGoal
  baseState.restore

  /- Try each usable local declaration independently from the same base state. -/
  let mut expansions := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then
      continue
    baseState.restore

    /- Peel explicit and implicit forall binders to expose the proposition being proved. -/
    let ⟨_, _, ty⟩ ← forallMetaTelescope (← instantiateMVars decl.type)
    if ! (← Meta.isProp ty) then continue
    have ty : Q(Prop) := ty

    /- Bridge the Lean proposition into the current Iris BI before probing apply premises. -/
    let hyp ← mkFreshExprMVarQ prop
    match ← ProofMode.trySynthInstanceQ q(AsEmpValid .into $ty .in $prop .in $bi $hyp) with
    | .none | .undef => continue
    | .some _ =>
      let some premises ← collectIntoWandPremises? (bi := bi) q(true) hyp target
        | continue
      let (goals, fullContextIrisSubgoals) ← mkChildren irisGoal tag irisGoal.hyps premises
      expansions := expansions.push {
        source := .lean decl.userName decl.fvarId
        goals
        fullContextIrisSubgoals
        postState := ← saveState
      }
  baseState.restore
  return expansions

/- Search stage work -/
def run (input : RuleInput) : SearchM Q RuleOutput := do
  /- Collect possible hypothesis that can be applied in current goal -/
  let goal := input.goal
  let expansions ← liftM do
    restoreState input.state
    goal.withContext do
      let goalType ← instantiateMVars (← goal.getType)
      let some irisGoal := parseIrisGoal? goalType
        | throwError "iaesop: applyHyps rule search must work in iris proof-mode context"
      let tag ← goal.getTag
      let baseState ← saveState
      let irisExpansions ←
        collectFromIris irisGoal tag baseState irisGoal.hyps
      let leanExpansions ←
        collectFromLean irisGoal tag baseState
      return irisExpansions ++ leanExpansions
  if expansions.isEmpty then return {}

  /- Construct corresponding Rapp specs for each probed hypothesis -/
  let specs ← expansions.mapM λ expansion => do
    dbg_trace s!"applyHyps selected {expansion.source.name} and generated {expansion.goals.size} goals"
    for irisGoal in expansion.fullContextIrisSubgoals do
      let targetFmt ← liftM <| ppExpr irisGoal.goal
      dbg_trace s!"  applyHyps child target: {targetFmt.pretty}"
    return {
      goals := expansion.goals
      postState := expansion.postState
      successPossibility := .hundred
      effect :=
        if expansion.goals.isEmpty then
          some (.closeGoal expansion.source.usedHyp?)
        else
          some (.contextManagement
            expansion.fullContextIrisSubgoals expansion.source.usedHyp?)
    }
  return RuleOutput.ofRappSpecs specs

def replay (input : RuleReplayInput) : ProofModeM (Array MVarId) := do
  return #[input.goal]

end Iris.ProofMode.Aesop.Rule.ApplyHyps
