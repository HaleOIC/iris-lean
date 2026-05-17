module

public meta import Iris.ProofMode.Aesop.Rule.Builtin.ApplyHyps
public meta import Iris.ProofMode.Aesop.Rule.Builtin.IMod
public meta import Iris.ProofMode.Aesop.Rule.Builtin.IModIntro
public meta import Iris.ProofMode.Aesop.Rule.Builtin.IExact
public meta import Iris.ProofMode.Aesop.Rule.Builtin.IPureIntro
public meta import Iris.ProofMode.Aesop.Rule.Builtin.Identity
public meta import Iris.ProofMode.Aesop.Rule.Builtin.Main
public meta import Iris.ProofMode.Aesop.Search.Normalization
public meta import Iris.ProofMode.Aesop.Search.RuleSelection

public meta section

namespace Iris.ProofMode.Aesop

variable {Q : Type} [Queue Q]

private def runRuleSpecs (parentRef : GoalRef) (matchResult : RuleMatch) :
    SearchM Q (Array RappSpec) := do
  if matchResult.rule.id == identityRuleId then
    Rule.Builtin.Identity.run parentRef matchResult
  else if matchResult.rule.id == iexactRuleId then
    Rule.Builtin.IExact.run parentRef matchResult
  else if matchResult.rule.id == applyHypsRuleId then
    Rule.Builtin.ApplyHyps.run parentRef matchResult
  else if matchResult.rule.id == ipureIntroRuleId then
    Rule.Builtin.IPureIntro.run parentRef matchResult
  else if matchResult.rule.id == imodIntroRuleId then
    Rule.Builtin.IModIntro.run parentRef matchResult
  else if matchResult.rule.id == imodRuleId then
    Rule.Builtin.IMod.run parentRef matchResult
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
