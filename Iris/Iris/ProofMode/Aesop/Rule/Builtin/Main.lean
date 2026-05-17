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

def ipureIntroRuleId : RuleId where
  name := `ipure_intro
  kind := .apply
  phase := .safe
  scope := .global

def ipureIntroRuleName : RuleName where
  name := `ipure_intro
  phase := .safe
  builder := .ipureIntro

def ipureIntroRule : Rule RegularRule where
  id := ipureIntroRuleId
  indexingMode := .unindexed
  payload := RegularRule.mkSafe ipureIntroRuleName

def imodIntroRuleId : RuleId where
  name := `imodintro
  kind := .apply
  phase := .safe
  scope := .global

def imodIntroRuleName : RuleName where
  name := `imodintro
  phase := .safe
  builder := .imodintro

def imodIntroRule : Rule RegularRule where
  id := imodIntroRuleId
  indexingMode := .unindexed
  payload := RegularRule.mkSafe imodIntroRuleName

def imodRuleId : RuleId where
  name := `imod
  kind := .apply
  phase := .safe
  scope := .global

def imodRuleName : RuleName where
  name := `imod
  phase := .safe
  builder := .imod

def imodRule : Rule RegularRule where
  id := imodRuleId
  indexingMode := .unindexed
  payload := RegularRule.mkSafe imodRuleName

def builtinRuleIndex : Index RegularRule :=
  ({} : Index RegularRule)
    |>.add identityRule identityRule.indexingMode
    |>.add iexactRule iexactRule.indexingMode
    |>.add applyHypsRule applyHypsRule.indexingMode
    |>.add ipureIntroRule ipureIntroRule.indexingMode
    |>.add imodIntroRule imodIntroRule.indexingMode
    |>.add imodRule imodRule.indexingMode

end Iris.ProofMode.Aesop
