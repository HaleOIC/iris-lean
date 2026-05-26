module

public meta import Iris.ProofMode.Aesop.Index.Query
public meta import Iris.ProofMode.Aesop.Rule.Common.ApplyHyps
public meta import Iris.ProofMode.Aesop.Rule.Common.Identity
public meta import Iris.ProofMode.Aesop.Rule.Common.IMod
public meta import Iris.ProofMode.Aesop.Rule.Common.IPureIntro
public meta import Iris.ProofMode.Aesop.Rule.Common.iExist
public meta import Iris.ProofMode.Aesop.Rule.Common.ISplit

public meta section

namespace Iris.ProofMode.Aesop

namespace RuleRunnerDescr

def run {Q : Type} [Queue Q] : RuleRunnerDescr → RuleRunner Q
  | .identity => Rule.Identity.run
  | .applyHyps => Rule.ApplyHyps.run
  | .imod => Rule.IMod.run
  | .ipureIntro => Rule.IPureIntro.run
  | .iExist => Rule.IExist.run
  | .isplit => Rule.ISplit.run
  | _ => λ _ => return {}

def replay : RuleRunnerDescr → RuleReplayer
  | .identity => Rule.Identity.replay
  | .applyHyps => Rule.ApplyHyps.replay
  | .imod => Rule.IMod.replay
  | .ipureIntro => Rule.IPureIntro.replay
  | .iExist => Rule.IExist.replay
  | .isplit => Rule.ISplit.replay
  | _ => λ input => return #[input.goal]

end RuleRunnerDescr

def commonIdentityRuleId : RuleId where
  name := `identity
  kind := .forward
  phase := .safe
  scope := .global

def commonIdentityRule : Rule RuleInfo where
  id := commonIdentityRuleId
  indexingMode := .unindexed
  info := RuleInfo.ofBuilder .identity

def commonApplyHypsRuleId : RuleId where
  name := `applyHyps
  kind := .apply
  phase := .safe
  scope := .global

def commonApplyHypsRule : Rule RuleInfo where
  id := commonApplyHypsRuleId
  indexingMode := .unindexed
  info := RuleInfo.ofBuilder .applyHyps

def commonIPureIntroRuleId : RuleId where
  name := `ipureIntro
  kind := .apply
  phase := .safe
  scope := .global

def commonIPureIntroRule : Rule RuleInfo where
  id := commonIPureIntroRuleId
  indexingMode := .unindexed
  info := RuleInfo.ofBuilder .ipureIntro

def commonIExistRuleId : RuleId where
  name := `iExist
  kind := .apply
  phase := .safe
  scope := .global

def commonIExistRule : Rule RuleInfo where
  id := commonIExistRuleId
  indexingMode := .unindexed
  info := RuleInfo.ofBuilder .iExist

def commonIModRuleId : RuleId where
  name := `imod
  kind := .apply
  phase := .safe
  scope := .global

def commonIModRule : Rule RuleInfo where
  id := commonIModRuleId
  indexingMode := .unindexed
  info := RuleInfo.ofBuilder .imod

def commonISplitRuleId : RuleId where
  name := `isplit
  kind := .apply
  phase := .safe
  scope := .global

def commonISplitRule : Rule RuleInfo where
  id := commonISplitRuleId
  indexingMode := .unindexed
  info := RuleInfo.ofBuilder .isplit

def commonRuleIndex : Index RuleInfo :=
  ({} : Index RuleInfo)
    |>.add commonIdentityRule commonIdentityRule.indexingMode
    |>.add commonApplyHypsRule commonApplyHypsRule.indexingMode
    |>.add commonIModRule commonIModRule.indexingMode
    |>.add commonIPureIntroRule commonIPureIntroRule.indexingMode
    |>.add commonIExistRule commonIExistRule.indexingMode
    |>.add commonISplitRule commonISplitRule.indexingMode

end Iris.ProofMode.Aesop
