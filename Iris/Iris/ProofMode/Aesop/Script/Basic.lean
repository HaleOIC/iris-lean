module

public import Lean.Meta.Basic

public section

open Lean Lean.Meta

namespace Iris.ProofMode.Aesop.Script

structure LazyStep where
  preState : SavedState
  preGoal : MVarId
  postState : SavedState
  postGoals : Array MVarId

end Script
