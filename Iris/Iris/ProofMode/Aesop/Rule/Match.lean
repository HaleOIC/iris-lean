module

public import Batteries.Data.Array.Basic
public import Iris.ProofMode.Aesop.Rule.Data

public section

namespace Iris.ProofMode.Aesop

open Lean

inductive IndexMatchLocation
  | target
  | hyp (fvarId : FVarId)
  deriving Inhabited, BEq

structure RulePatternSubst where
  exprs : Array Expr := #[]
  levels : Array Level := #[]
  deriving Inhabited

structure IndexMatchResult (α : Type) where
  rule : α
  locations : Array IndexMatchLocation := #[]
  patternSubsts? : Option (Array RulePatternSubst) := none
  deriving Inhabited

abbrev RuleMatch := IndexMatchResult RegularRule

abbrev RuleQueue := Subarray RuleMatch

namespace RuleQueue

instance : EmptyCollection RuleQueue :=
  inferInstanceAs $ EmptyCollection (Subarray _)

instance : Inhabited RuleQueue :=
  inferInstanceAs $ Inhabited (Subarray _)

def ofArray (matchResults : Array RuleMatch) : RuleQueue :=
  matchResults.toSubarray

def pop? (queue : RuleQueue) : Option (RuleMatch × RuleQueue) :=
  Subarray.popHead? queue

end RuleQueue

end Iris.ProofMode.Aesop
