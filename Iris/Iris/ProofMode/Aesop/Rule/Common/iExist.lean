module

public meta import Iris.ProofMode.Aesop.Rule.Commit.Basic
public meta import Iris.ProofMode.Tactics.Exists

public meta section

namespace Iris.ProofMode.Aesop.Rule.IExist

open Lean Meta Qq Std
open Iris.BI
open Iris.ProofMode

variable {Q : Type} [Queue Q]

/- Search only checks that the target has a `FromExists` view and then exposes
the existential body with a fresh witness metavariable for later rules to solve. -/
def run (input : RuleInput) : SearchM Q RuleOutput := do
  let goal := input.goal
  let some (child, postState) ← liftM (show ProofModeM (Option (SubGoal × SavedState)) from do
    input.state.restore
    goal.withContext do
      let goalType ← instantiateMVars (← goal.getType)
      let some irisGoal := parseIrisGoal? goalType
        | return none
      let { prop, goal := target, hyps .. } := irisGoal
      let v ← mkFreshLevelMVar
      let α ← mkFreshExprMVarQ q(Sort v)
      let Φ ← mkFreshExprMVarQ q($α → $prop)
      let .some (_, _) ← ProofMode.trySynthInstanceQ q(FromExists $target $Φ)
        | return none

      -- Keep the same Iris context; only the target changes from `∃ x, Φ x` to `Φ ?x`.
      let witness : Q($α) ← mkFreshExprMVar α
      let childTarget : Q($prop) := q($Φ $witness)
      let childExpr ← mkBIGoal hyps childTarget (← goal.getTag)
      return some (
        { goal := childExpr.mvarId!, addedFVars := {}, removedFVars := {} },
        ← liftM (m := MetaM) saveState
      ))
    | return {}
  return RuleOutput.ofRappSpec {
    goals := #[child]
    postState
    successPossibility := .hundred
    effect := none
  }

/- Replay rebuilds the same existential view and then assigns the parent goal
using the generated child proof followed by `exists_intro'`. -/
def replay (input : RuleReplayInput) : ProofModeM (Array MVarId) := do
  input.goal.withContext do
    let goalType ← instantiateMVars (← input.goal.getType)
    let some irisGoal := parseIrisGoal? goalType
      | throwError "iaesop(baseline): iexist replay expected an Iris goal"
    let { prop, e, hyps, goal := target, .. } := irisGoal
    have e : Q($prop) := e
    have target : Q($prop) := target
    let v ← mkFreshLevelMVar
    let α : Q(Sort v) ← mkFreshExprMVarQ q(Sort v)
    let Φ : Q($α → $prop) ← mkFreshExprMVarQ q($α → $prop)
    let .some (_, _) ← ProofMode.trySynthInstanceQ q(FromExists $target $Φ)
      | throwError "iaesop(baseline): iexist replay could not view the target as existential"
    let witness : Q($α) ← mkFreshExprMVar α
    let childTarget : Q($prop) := q($Φ $witness)
    let childProof : Q($e ⊢ $childTarget) ← mkBIGoal hyps childTarget (← input.goal.getTag)
    let targetRfl : Q($target ⊢ $target) := q(.rfl)
    let introProof : Q($childTarget ⊢ $target) := q(exists_intro' $witness $targetRfl)
    input.goal.assign q(($childProof).trans $introProof)
    return #[childProof.mvarId!]

end Iris.ProofMode.Aesop.Rule.IExist
