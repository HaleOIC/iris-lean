module

public meta import Iris.ProofMode.Aesop.Search.Types
public meta import Iris.ProofMode.Aesop.Search.SearchM

public meta section

namespace Iris.ProofMode.Aesop.Search

open Iris.ProofMode.Aesop.Tree

variable {Q : Type} [Queue Q]

def normalizeGoal (_gref : GoalRef) : SearchM Q Unit := do
  return

end Search
