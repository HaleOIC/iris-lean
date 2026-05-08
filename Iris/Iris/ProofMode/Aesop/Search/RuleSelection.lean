module

public meta import Iris.ProofMode.Aesop.Index.Query
public meta import Iris.ProofMode.Aesop.Search.SearchM

public meta section

namespace Iris.ProofMode.Aesop

variable {Q : Type} [Queue Q]

def selectRules (parentRef : GoalRef) : SearchM Q RuleQueue := do
  return (← parentRef.get).rulesQueue

def selectRulesFromIndex (index : Index RegularRule) (parentRef : GoalRef) :
    SearchM Q RuleQueue := do
  let parent ← parentRef.get
  return RuleQueue.ofArray (← Index.queryMVar index parent.preNormGoal)

end Iris.ProofMode.Aesop
