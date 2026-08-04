module

public meta import Iris.ProofMode.Aesop.Search.Shared.CoreM
public meta import Iris.ProofMode.Aesop.Search.Shared.Types
public meta import Iris.ProofMode.Aesop.Rule.Types.Runner

public meta section

namespace Iris.ProofMode.Aesop

open Lean Meta Std

variable {Q : Type} [Queue Q]

/- Get normalized MVarId and SavedState -/
def normalizedGoalAndState (ruleName : String) (parent : Goal) :
    CoreM Q (MVarId × SavedState) := do
  match parent.normalizationState with
  | .normal postGoal postState .. =>
    return (postGoal, postState)
  | .provenByNorm .. =>
    throwError "iaesop: internal error: {ruleName} ran on a goal already proven by normalization"
  | .notNormal =>
    throwError "iaesop: internal error: {ruleName} ran on a non-normalized goal"

/- Make up rule input from given info -/
def mkRuleInput (ruleName : String) (parentRef : GoalRef)
    (matchResult : RuleMatch) : CoreM Q (Option RuleInput) := do
  let parent ← parentRef.get
  let (goal, state) ← normalizedGoalAndState ruleName parent
  let mvars ← liftM (m := MetaM) do
    let preState ← saveState
    state.restore
    let mvars ← goal.getMVarDependencies
    preState.restore
    return mvars
  return some { goal, depth := parent.depth, state, mvars := mvars.toArray, matchResult }

end Iris.ProofMode.Aesop
