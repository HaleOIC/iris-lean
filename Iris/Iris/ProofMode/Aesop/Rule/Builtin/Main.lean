module

public meta import Iris.ProofMode.Aesop.Index.Query

public meta section

namespace Iris.ProofMode.Aesop

-- namespace RuleRunnerDescr

-- def run {Q : Type} [Queue Q] : RuleRunnerDescr → RuleRunner Q
--   | .identity => Rule.Builtin.Identity.run
--   | .iexact => Rule.Builtin.IExact.run
--   | .applyHyps => Rule.Builtin.ApplyHyps.run
--   | .ipureIntro => Rule.Builtin.IPureIntro.run
--   | .imodIntro => Rule.Builtin.IModIntro.run
--   | .imod => Rule.Builtin.IMod.run
--   | .custom => fun _ => return {}

-- end RuleRunnerDescr

-- def identityRuleId : RuleId where
--   name := `identity
--   kind := .forward
--   phase := .safe
--   scope := .global

-- def identityRule : Rule RuleInfo where
--   id := identityRuleId
--   indexingMode := .unindexed
--   info := RuleInfo.ofBuilder .identity

-- def iexactRuleId : RuleId where
--   name := `iexact
--   kind := .apply
--   phase := .safe
--   scope := .global

-- def iexactRule : Rule RuleInfo where
--   id := iexactRuleId
--   indexingMode := .unindexed
--   info := RuleInfo.ofBuilder .iexact

-- def applyHypsRuleId : RuleId where
--   name := `applyHyps
--   kind := .apply
--   phase := .safe
--   scope := .global

-- def applyHypsRule : Rule RuleInfo where
--   id := applyHypsRuleId
--   indexingMode := .unindexed
--   info := RuleInfo.ofBuilder .applyHyps

-- def ipureIntroRuleId : RuleId where
--   name := `ipure_intro
--   kind := .apply
--   phase := .safe
--   scope := .global

-- def ipureIntroRule : Rule RuleInfo where
--   id := ipureIntroRuleId
--   indexingMode := .unindexed
--   info := RuleInfo.ofBuilder .ipureIntro

-- def imodIntroRuleId : RuleId where
--   name := `imodintro
--   kind := .apply
--   phase := .safe
--   scope := .global

-- def imodIntroRule : Rule RuleInfo where
--   id := imodIntroRuleId
--   indexingMode := .unindexed
--   info := RuleInfo.ofBuilder .imodintro

-- def imodRuleId : RuleId where
--   name := `imod
--   kind := .apply
--   phase := .safe
--   scope := .global

-- def imodRule : Rule RuleInfo where
--   id := imodRuleId
--   indexingMode := .unindexed
--   info := RuleInfo.ofBuilder .imod

def builtinRuleIndex : Index RuleInfo :=
  ({} : Index RuleInfo)
    -- |>.add identityRule identityRule.indexingMode
    -- |>.add iexactRule iexactRule.indexingMode
    -- |>.add applyHypsRule applyHypsRule.indexingMode
    -- |>.add ipureIntroRule ipureIntroRule.indexingMode
    -- |>.add imodIntroRule imodIntroRule.indexingMode
    -- |>.add imodRule imodRule.indexingMode

-- end Iris.ProofMode.Aesop
