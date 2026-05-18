module

public meta import Iris.ProofMode.Aesop.Search.SearchM
public meta import Iris.ProofMode.Aesop.Search.Types
public meta import Iris.ProofMode.Aesop.Rule.Commit.Baseline
public meta import Iris.ProofMode.Aesop.Rule.Commit.Builtin
public meta import Iris.ProofMode.Aesop.Rule.Types.Runner

public meta section

namespace Iris.ProofMode.Aesop

open Lean Meta Std

variable {Q : Type} [Queue Q]

/- Get normalized MVarId and SavedState -/
def normalizedGoalAndState (ruleName : String) (parent : Goal) :
    SearchM Q (MVarId × SavedState) := do
  match parent.normalizationState with
  | .normal postGoal postState .. =>
    return (postGoal, postState)
  | .provenByNorm .. =>
    throwError "iaesop: internal error: {ruleName} ran on a goal already proven by normalization"
  | .notNormal =>
    throwError "iaesop: internal error: {ruleName} ran on a non-normalized goal"

/- Make up rule input from given info -/
def mkRuleInput (ruleName : String) (parentRef : GoalRef)
    (matchResult : RuleMatch) : SearchM Q (Option RuleInput) := do
  let parent ← parentRef.get
  let (goal, state) ← normalizedGoalAndState ruleName parent
  let mvars ← goal.getMVarDependencies
  return some { goal, state, mvars := mvars.toArray, matchResult }

def commitRuleOutput (gref : GoalRef) (output : RuleOutput) : SearchM Q RuleResult := do
  if output.rappSepcs.isEmpty then return .failed

  -- Collect new added RappRefs and Subgoals and update state
  let mut rappRefs := #[]
  let mut goalsToEnqueue := #[]
  for spec in output.rappSepcs do
    let (rappRef, goalRefs) ←
      if (← readThe SearchM.Context).config.baseline? then
        Rule.Commit.Baseline.addRappSpec gref spec
      else
        Rule.Commit.Builtin.addRappSpec gref spec
    rappRefs := rappRefs.push rappRef
    goalsToEnqueue := goalsToEnqueue ++ goalRefs

  let provenBy? ← rappRefs.findSomeM? λ rappRef => do
    let rapp ← rappRef.get
    if rapp.state.isProven then
    -- TODO: This only collects the hypothesis consumed by the current `rapp`.
    -- If this `rapp` is proven via downstream applications, we should traverse
    -- the corresponding proof subtree and collect all hypotheses consumed there.
      return some rapp.consumedSpatialHyp?.toArray
    return none

  gref.modify λ g =>
    let g := g.setChildren (g.children ++ rappRefs)
    match provenBy? with
    | some used => g.setState (.provenByRuleApplication used)
    | none => g
  enqueueGoals goalsToEnqueue

  match provenBy? with
  | some _ => pure $ RuleResult.proved rappRefs
  | none => pure $ .succeeded rappRefs

end Iris.ProofMode.Aesop
