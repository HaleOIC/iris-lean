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
  let mvars ← liftM (m := MetaM) do
    let preState ← saveState
    state.restore
    let mvars ← goal.getMVarDependencies
    preState.restore
    return mvars
  return some { goal, depth := parent.depth, state, mvars := mvars.toArray, matchResult }

def commitRuleOutput (gref : GoalRef) (usedRule : Rule RuleInfo)
    (output : RuleOutput) : SearchM Q RuleResult := do
  if output.rappSepcs.isEmpty then return .failed

  -- Collect new added RappRefs and Subgoals and update state
  let mut rappRefs := #[]
  let mut goalsToEnqueue := #[]
  for spec in output.rappSepcs do
    let (rappRef, goalRefs) ←
      if (← readThe SearchM.Context).config.baseline? then
        Baseline.mkRappSpec gref usedRule spec
      else
        Rule.Commit.Builtin.mkRappSpec gref usedRule spec
    rappRefs := rappRefs.push rappRef
    goalsToEnqueue := goalsToEnqueue ++ goalRefs

  let provenBy? ← rappRefs.findM? λ rappRef => do
    let rapp ← rappRef.get
    return rapp.state.isProven

  gref.modify λ g =>
    let g := g.setChildren (g.children ++ rappRefs)
    match provenBy? with
    | some _ => g.setState .provenByRuleApplication
    | none => g
  enqueueGoals goalsToEnqueue

  match provenBy? with
  | some _ => pure $ RuleResult.proved rappRefs
  | none => pure $ .succeeded rappRefs

end Iris.ProofMode.Aesop
