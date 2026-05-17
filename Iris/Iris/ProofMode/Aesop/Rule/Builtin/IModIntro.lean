module

public meta import Iris.ProofMode.Aesop.Rule.Common
public meta import Iris.ProofMode.Tactics.ModIntro

public meta section

namespace Iris.ProofMode.Aesop.Rule.Builtin.IModIntro

open Lean Meta Qq Std
open Iris.BI
open Iris.ProofMode
open Iris.ProofMode.Aesop

variable {Q : Type} [Queue Q]

private def runCore (goal : MVarId) :
    ProofModeM (Option (ChildGoalSpec × SavedState)) := do
  let preState ← liftM (show MetaM SavedState from saveState)
  let prePMState ← getThe ProofModeM.State
  try
    goal.withContext do
      let goalType ← instantiateMVars (← goal.getType)
      let some { hyps, goal := target, .. } := parseIrisGoal? goalType
        | return none
      let childRef ← IO.mkRef (none : Option MVarId)
      let proof ← iModIntroCore hyps target (← `(term| _))
        fun hyps' target' => do
          let childExpr ← mkBIGoal hyps' target' (← goal.getTag)
          childRef.set (some childExpr.mvarId!)
          return childExpr
      let some childGoal := ← childRef.get
        | throwError "iaesop: internal error: imodintro did not generate a goal"
      goal.assign proof
      let child ← liftM <| mkChildGoalSpec childGoal
      return some (child, ← liftM (show MetaM SavedState from saveState))
  catch _ =>
    set prePMState
    liftM <| preState.restore
    return none

def run (input : RuleInput) : SearchM Q RuleOutput := do
  let goal := input.goal
  let state := input.state
  let result? ← liftM (show ProofModeM (Option (ChildGoalSpec × SavedState)) from do
    liftM <| state.restore
    runCore goal)
  let some (child, postState) := result?
    | return {}
  return RuleOutput.single {
    rappState := .unknown
    obunState := .unknown
    obunKind := .plain
    childGoals := #[child]
    fullContextIrisSubgoals := #[child.irisGoal]
    consumedSpatialHyp? := none
    finalizedSpatialSplits := #[]
    metaState := postState
  }

end Iris.ProofMode.Aesop.Rule.Builtin.IModIntro
