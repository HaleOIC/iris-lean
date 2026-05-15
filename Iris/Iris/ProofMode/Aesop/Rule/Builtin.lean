module

public meta import Iris.ProofMode.Aesop.Index.Query
public meta import Iris.ProofMode.Aesop.Rule.Common

public meta section

namespace Iris.ProofMode.Aesop

def identityRuleId : RuleId where
  name := `identity
  kind := .forward
  phase := .safe
  scope := .global

def identityRuleName : RuleName where
  name := `identity
  phase := .safe
  builder := .identity

def identityRule : Rule RegularRule where
  id := identityRuleId
  indexingMode := .unindexed
  payload := RegularRule.mkSafe identityRuleName

def iexactRuleId : RuleId where
  name := `iexact
  kind := .apply
  phase := .safe
  scope := .global

def iexactRuleName : RuleName where
  name := `iexact
  phase := .safe
  builder := .iexact

def iexactRule : Rule RegularRule where
  id := iexactRuleId
  indexingMode := .unindexed
  payload := RegularRule.mkSafe iexactRuleName

def applyHypsRuleId : RuleId where
  name := `applyHyps
  kind := .apply
  phase := .safe
  scope := .global

def applyHypsRuleName : RuleName where
  name := `applyHyps
  phase := .safe
  builder := .applyHyps

def applyHypsRule : Rule RegularRule where
  id := applyHypsRuleId
  indexingMode := .unindexed
  payload := RegularRule.mkSafe applyHypsRuleName

def builtinRuleIndex : Index RegularRule :=
  ({} : Index RegularRule)
    |>.add identityRule identityRule.indexingMode
    |>.add iexactRule iexactRule.indexingMode
    |>.add applyHypsRule applyHypsRule.indexingMode

end Iris.ProofMode.Aesop
