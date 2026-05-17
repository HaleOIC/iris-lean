module

public import Batteries.Data.Array.Basic
public meta import Iris.ProofMode.Aesop.Index.Types
public meta import Iris.ProofMode.Aesop.Rule.Types.Rule
public import Iris.ProofMode.Aesop.Rule.Types.Info

public section

namespace Iris.ProofMode.Aesop

abbrev RuleMatch := IndexMatchResult (Rule RuleInfo)

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
