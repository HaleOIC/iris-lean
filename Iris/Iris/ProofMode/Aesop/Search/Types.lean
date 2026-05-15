module

public meta import Iris.ProofMode.Aesop.Tree.Basic

public meta section

namespace Iris.ProofMode.Aesop

open Lean Lean.Meta

inductive RuleResult
  | proved (newRapps : Array RappRef)
  | succeeded (newRapps : Array RappRef)
  | failed
  deriving Inhabited

namespace RuleResult

protected def isSuccessful
  | proved .. | succeeded .. => true
  | failed => false

end RuleResult

structure CopiedGoalInfo where
  index : Nat
  goal : MVarId
  mvars : Std.HashSet MVarId
  deriving Inhabited

end Aesop
