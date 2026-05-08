module

public meta import Iris.ProofMode.Aesop.Tree.Basic

public meta section

namespace Iris.ProofMode.Aesop.Search

open Lean Lean.Meta
open Iris.ProofMode.Aesop.Tree

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

end Search
