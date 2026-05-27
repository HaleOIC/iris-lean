module

public meta import Iris.ProofMode.Aesop.Rule.Commit.Basic
public meta import Iris.ProofMode.Tactics.ModIntro

public meta section

namespace Iris.ProofMode.Aesop.Rule.IModIntro

open Lean Meta Qq Std
open Iris.ProofMode

variable {Q : Type} [Queue Q]

private structure IModIntroExpansion where
  goal : SubGoal
  childIrisGoal : IrisGoal
  postState : SavedState

/- Try to make an expansion based on current target -/
private def mkExpansion? (goal : MVarId) (irisGoal : IrisGoal) :
    ProofModeM (Option IModIntroExpansion) := do
  let preState ← liftM (m := MetaM) saveState
  try
    let childRef ← IO.mkRef (none : Option (SubGoal × IrisGoal))
    let _ ← iModIntroCore irisGoal.hyps irisGoal.goal (← `(_)) λ hyps newTarget => do
      let newGoal ← mkBIGoal hyps newTarget (← goal.getTag)
      let newGoalMVarId := newGoal.mvarId!
      let newIrisGoal ← newGoalMVarId.withContext do
        let some irisGoal := parseIrisGoal? <| ← instantiateMVars (← newGoalMVarId.getType)
          | throwError "iaesop: imodintro generated a non-Iris child goal"
        return irisGoal
      childRef.set (some ({ goal := newGoalMVarId, addedFVars := {}, removedFVars := {}}, newIrisGoal))
      return newGoal
    let some (child, childIrisGoal) := ← childRef.get
      | throwError "iaesop: imodintro did not generate a child goal"
    return some {
      goal := child
      childIrisGoal
      postState := ← liftM (m := MetaM) saveState
    }
  catch _ =>
    liftM <| preState.restore
    return none

/- Search for the possibility of `imodintro` application -/
def run (input : RuleInput) : SearchM Q RuleOutput := do
  let goal := input.goal
  let some expansion ← liftM (m := ProofModeM) do
    input.state.restore
    goal.withContext do
      let goalType ← instantiateMVars (← goal.getType)
      let some irisGoal := parseIrisGoal? goalType
        | throwError "iaesop: imodintro rule search must work in iris proof-mode context"
      mkExpansion? goal irisGoal
    | return {}
  let targetFmt ← liftM <| goal.withContext <| ppExpr expansion.childIrisGoal.goal
  dbg_trace s!"imodintro generated 1 goal"
  dbg_trace s!"  imodintro child target: {targetFmt.pretty}"
  return RuleOutput.ofRappSpec {
    goals := #[expansion.goal]
    postState := expansion.postState
    successPossibility := .hundred
    effect := default
  }

/- [Note] Make sure you are in the correct context -/
def replay (input : RuleReplayInput) : ProofModeM (Array MVarId) := do
  let obun ← input.rapp.children.get
  if obun.goals.size != 1 then
    throwError s!"iaesop(baseline): imodintro replay expected one child goal, got {obun.goals.size}"
  input.goal.withContext do
    let goalType ← instantiateMVars (← input.goal.getType)
    let some irisGoal := parseIrisGoal? goalType
      | throwError "iaesop(baseline): imodintro replay expected an Iris goal"
    let childRef ← IO.mkRef (none : Option MVarId)
    let proof ←
      iModIntroCore irisGoal.hyps irisGoal.goal (← `(_)) fun hyps childTarget => do
        let childExpr ← mkBIGoal hyps childTarget (← input.goal.getTag)
        childRef.set (some childExpr.mvarId!)
        return childExpr
    input.goal.assign proof
    let some childGoal := ← childRef.get
      | throwError "iaesop(baseline): imodintro replay did not generate a child goal"
    return #[childGoal]

end Iris.ProofMode.Aesop.Rule.IModIntro
