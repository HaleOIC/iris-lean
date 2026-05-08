module

public meta import Iris.ProofMode.Aesop.Search.SearchM
public meta import Iris.ProofMode.Aesop.Search.Types
public meta import Iris.ProofMode.Aesop.Search.Normalization
public meta import Iris.ProofMode.Aesop.Search.RuleSelection

public meta section

namespace Iris.ProofMode.Aesop

open Lean Tactic Meta

variable {Q : Type} [Queue Q]

private def runRule (_parentRef : GoalRef) (_matchResult : RuleMatch) :
    SearchM Q RuleResult := do
  -- [TODO] connect this to the actual rule application implementation.
  return .failed

private partial def runFirstRule (parentRef : GoalRef) : SearchM Q RuleResult := do
  let ruleCandidates ← selectRules parentRef
  let (remainingRules, result) ← pickLoop ruleCandidates
  parentRef.modify λ g => g.setRulesQueue remainingRules
  -- [Note] dropped the "mark unprovable" here, we can postpone it until
  -- Search Main loop (I suppose)
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
  -- [Note] skip the normalization stage for prototype
  -- if !(← (← gref.get).isNormalized) then normalizeGoal gref
  if (← gref.get).normalizationState.isProvenByNorm then
    return .proved #[]

  -- run first rule that selected and return back result
  runFirstRule gref

end Aesop
