module

public import Batteries.Data.Array.Basic
public meta import Iris.ProofMode.Aesop.Index.Types
public import Iris.ProofMode.Aesop.Rule.Basic
public import Iris.ProofMode.Aesop.Rule.Data

public section

namespace Iris.ProofMode.Aesop

abbrev RuleMatch := IndexMatchResult (Rule RegularRule)

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
