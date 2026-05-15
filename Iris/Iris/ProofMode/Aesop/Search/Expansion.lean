module

public meta import Iris.ProofMode.Aesop.Rule.ApplyHyps
public meta import Iris.ProofMode.Aesop.Rule.Builtin
public meta import Iris.ProofMode.Aesop.Rule.IMod
public meta import Iris.ProofMode.Aesop.Rule.IModIntro
public meta import Iris.ProofMode.Aesop.Rule.IExact
public meta import Iris.ProofMode.Aesop.Rule.IPureIntro
public meta import Iris.ProofMode.Aesop.Rule.Identity
public meta import Iris.ProofMode.Aesop.Search.Normalization
public meta import Iris.ProofMode.Aesop.Search.RuleSelection

public meta section

namespace Iris.ProofMode.Aesop

variable {Q : Type} [Queue Q]

private def runRuleSpecs (parentRef : GoalRef) (matchResult : RuleMatch) :
    SearchM Q (Array RappSpec) := do
  if matchResult.rule.id == identityRuleId then
    Rule.Identity.run parentRef matchResult
  else if matchResult.rule.id == iexactRuleId then
    Rule.IExact.run parentRef matchResult
  else if matchResult.rule.id == applyHypsRuleId then
    Rule.ApplyHyps.run parentRef matchResult
  else if matchResult.rule.id == ipureIntroRuleId then
    Rule.IPureIntro.run parentRef matchResult
  else if matchResult.rule.id == imodIntroRuleId then
    Rule.IModIntro.run parentRef matchResult
  else if matchResult.rule.id == imodRuleId then
    Rule.IMod.run parentRef matchResult
  else
    return #[]

private def runRule (parentRef : GoalRef) (matchResult : RuleMatch) :
    SearchM Q RuleResult := do
  let specs ← runRuleSpecs parentRef matchResult
  addRappSpecs parentRef matchResult specs

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
