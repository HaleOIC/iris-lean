module

public meta import Iris.ProofMode.Aesop.Search.SearchM

public meta section

namespace Iris.ProofMode.Aesop.Search

open Iris.ProofMode.Aesop.Tree

variable {Q : Type} [Queue Q]

def selectRules (parentRef : GoalRef) : SearchM Q RuleQueue := do
  return (← parentRef.get).rulesQueue

end Iris.ProofMode.Aesop.Search
