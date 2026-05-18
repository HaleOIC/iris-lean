module

public meta import Iris.ProofMode.Aesop.Rule.Commit.Basic
public meta import Iris.ProofMode.Aesop.Rule.Common.Main
public meta import Iris.ProofMode.Aesop.Search.Normalization
public meta import Iris.ProofMode.Aesop.Search.RuleSelection

public meta section

namespace Iris.ProofMode.Aesop

variable {Q : Type} [Queue Q]

private def runRule (parentRef : GoalRef) (matchResult : RuleMatch) :
    SearchM Q RuleResult := do
  let some input ← mkRuleInput (toString matchResult.rule.id) parentRef matchResult
    | return .failed
  let output ← RuleRunnerDescr.ofInfo input.matchResult.rule.info |>.run input
  commitRuleOutput parentRef output

private partial def runFirstRule (parentRef : GoalRef) : SearchM Q RuleResult := do
  let ruleCandidates ← selectRules parentRef
  let (remainingRules, result) ← pickLoop ruleCandidates
  parentRef.modify λ g => g.setRulesQueue remainingRules
  return result
  where
    pickLoop (queue : RuleQueue) : SearchM Q (RuleQueue × RuleResult) := do
      let some (matchResult, queue) := RuleQueue.pop? queue
        | return (queue, .failed)
      let result ← runRule parentRef matchResult
      match result with
      | .proved .. | .succeeded .. => return (queue, result)
      | .failed => pickLoop queue

def expandGoal (gref : GoalRef) : SearchM Q RuleResult := do
  if !(← (← gref.get).isNormalized) then
    normalizeGoal gref
  if (← gref.get).normalizationState.isProvenByNorm then
    return .proved #[]
  runFirstRule gref

end Iris.ProofMode.Aesop
