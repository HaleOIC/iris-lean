module

public meta import Iris.ProofMode.Aesop.Rule.Commit.Basic
public meta import Iris.ProofMode.Tactics.Split

public meta section

namespace Iris.ProofMode.Aesop.Rule.ISplit

open Lean Meta Qq Std
open Iris.BI
open Iris.ProofMode

variable {Q : Type} [Queue Q]

private def mkAndChildren (goal : MVarId) :
    MetaM (Option (Array SubGoal × Array IrisGoal)) := do
  goal.withContext do
    let goalType ← instantiateMVars (← goal.getType)
    let some irisGoal := parseIrisGoal? goalType
      | throwError "iaesop: isplit must work in iris proof-mode context"
    let { prop, goal := target, .. } := irisGoal
    let lhs ← mkFreshExprMVarQ prop
    let rhs ← mkFreshExprMVarQ prop
    let .some _ ← trySynthInstanceProbeQ q(FromAnd $target $lhs $rhs)
      | return none
    let lhs : Q($prop) ← instantiateMVars lhs
    let rhs : Q($prop) ← instantiateMVars rhs
    let tag ← goal.getTag
    let mut children : Array SubGoal := #[]
    let mut fullContextIrisSubgoals : Array IrisGoal := #[]
    for target in #[lhs, rhs] do
      let irisGoal := { irisGoal with goal := target }
      let goalExpr ← mkFreshExprSyntheticOpaqueMVar (IrisGoal.toExpr irisGoal) tag
      let goal := goalExpr.mvarId!
      children := children.push { goal, addedFVars := {}, removedFVars := {} }
      fullContextIrisSubgoals := fullContextIrisSubgoals.push irisGoal
    return some (children, fullContextIrisSubgoals)

def run (input : RuleInput) : CoreM Q RuleOutput := do
  let goal := input.goal
  let (some (children, fullContextIrisSubgoals), postState) ← liftM do
      restoreState input.state
      let children? ← mkAndChildren goal
      let postState ← saveState
      return (children?, postState)
    | return {}

  trace[iaesop.tactic] s!"identity split target into {children.size} goals"
  for irisGoal in fullContextIrisSubgoals do
    let targetFmt ← liftM <| ppExpr irisGoal.goal
    trace[iaesop.tactic] s!"  identity child target: {targetFmt.pretty}"

  return RuleOutput.ofRappSpec {
    goals := children
    postState := postState
    successPossibility := .hundred
    effect := { action := some (.splitGoals fullContextIrisSubgoals)}
  }

/- [Note] Make sure you are in the correct context. -/
def replay (input : RuleReplayInput) : ProofModeM (Array MVarId) := do
  let obun ← input.rapp.children.get
  if obun.goals.size != 2 then
    throwError s!"iaesop(baseline): isplit replay expected two child goals, got {obun.goals.size}"
  input.goal.withContext do
    let goalType ← instantiateMVars (← input.goal.getType)
    let some { prop, hyps, goal := target, .. } := parseIrisGoal? goalType
      | throwError "iaesop(baseline): isplit replay expected an Iris goal"
    let Q1 ← mkFreshExprMVarQ prop
    let Q2 ← mkFreshExprMVarQ prop
    let some inst ← ProofModeM.trySynthInstanceQ q(FromAnd $target $Q1 $Q2)
      | throwError "iaesop(baseline): isplit replay could not view the target as a conjunction"
    let _ : Q(FromAnd $target $Q1 $Q2) := inst
    let tag ← input.goal.getTag
    let leftGoal ← mkBIGoal hyps Q1 tag
    let rightGoal ← mkBIGoal hyps Q2 tag
    input.goal.assign q(from_and_intro (Q := $target) $leftGoal $rightGoal)
    return #[leftGoal.mvarId!, rightGoal.mvarId!]

end Iris.ProofMode.Aesop.Rule.ISplit
