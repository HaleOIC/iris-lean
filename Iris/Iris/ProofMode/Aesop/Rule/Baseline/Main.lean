module

public meta import Iris.ProofMode.Aesop.Index.Query
public meta import Iris.ProofMode.Aesop.Rule.Common

public meta section

namespace Iris.ProofMode.Aesop

/- Template rule index for the baseline configuration.

Extend this file with baseline-specific rules and add them to
`baselineRuleIndex` below.
-/
def baselineRuleIndex : Index RuleInfo :=
  ({} : Index RuleInfo)

end Iris.ProofMode.Aesop
