module

public meta import Iris.ProofMode.Aesop.Rule.Common.Main
public meta import Iris.ProofMode.Aesop.Search.Normalization

public meta section

namespace Iris.ProofMode.Aesop.Baseline

open Lean Meta Qq Std

variable {Q : Type} [Queue Q]

private def replayRapp (rapp : Rapp) (goalMVarId : MVarId) :
    SearchM Q MVarId := do
  RuleRunnerDescr.ofInfo rapp.appliedRule.info |>.replay {
    goal := goalMVarId
    rapp
  }

/- Assign the proof term following the proven chain -/
/- [Note] We should follow the tree but with different goal (real replay stage) MVarId -/
private partial def assignProof (goal : Goal) (goalMVarId : MVarId): SearchM Q Unit := do
  /- First check the normalization stage's change -/
  let config := (← readThe SearchM.Context).config
  let result ← liftM (m := ProofModeM) do
    normalizeGoalMVar goalMVarId goal.depth config.maxNormIterations
      config.enableSimp? goal.unassignedMvars
  let some goalMVarId :=
      match result with
      | .proved => none
      | .changed goalMVarId => some goalMVarId
      | .unchanged => some goalMVarId
    | return ()

  /- Find an already proven Rapp node to replay -/
  let some rref ← goal.children.findM? λ rref => do
    let rapp ← rref.get
    return rapp.state.isProven && !rapp.isIrrelevant
  | throwError "iaesop(baseline): replay procedure could not find a proven rapp to move"

  /- Call the corresponding replay rules and find the next goal node in obun -/
  let rapp ← rref.get
  let goalMVarId ← RuleRunnerDescr.ofInfo rapp.appliedRule.info |>.replay
    { goal := goalMVarId, rapp }
  let childObun ← rapp.children.get
  let some nextGoalRef ← childObun.goals.findM? λ childRef => do
    let child ← childRef.get
    return child.state.isProven && !child.isIrrelevant
  | return ()
  assignProof (← nextGoalRef.get) goalMVarId

/- (Baseline) Replay proof entry point -/
public meta def replayProof : SearchM Q Unit := do
  let rootGoal ← (← getRootGoal).get
  if !rootGoal.state.isProven then
    throwError "iaesop(baseline): replay procedure reach an unproven goal"

  /- Make sure goal's mvarId has not been assigned -/
  let rootMVarId := rootGoal.normalizationState.normalizedGoal?.getD rootGoal.preNormGoal
  let assigned ← liftM (m := MetaM) rootMVarId.isAssignedOrDelayedAssigned
  if assigned then return

  /- Enter the replay context -/
  rootGoal.preNormState.restore
  assignProof rootGoal rootGoal.preNormGoal
