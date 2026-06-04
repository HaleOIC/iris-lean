module

public meta import Iris.ProofMode.Aesop.Rule.Commit.Basic
public meta import Iris.ProofMode.Tactics.HaveCore


public meta section

namespace Iris.ProofMode.Aesop.Rule.HaveHyps

open Lean Meta Qq Std Iris BI ProofMode

variable {Q : Type} [Queue Q]

/- Record information produced during expansion -/
private structure HaveHypsExpansion where
  usedHyp : AppliedHyp
  generatedHyp? : Option IrisHyp
  goals : Array SubGoal
  fullContextIrisSubgoals : Array IrisGoal
  postState : SavedState

def run (_input : RuleInput) : SearchM Q RuleOutput := do
  return {}

def replay (input : RuleReplayInput) : ProofModeM (Array MVarId) := do
  return #[input.goal]

end Iris.ProofMode.Aesop.Rule.HaveHyps
