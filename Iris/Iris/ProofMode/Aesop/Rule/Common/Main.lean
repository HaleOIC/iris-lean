module

public meta import Iris.ProofMode.Aesop.Index.Query
public meta import Iris.ProofMode.Aesop.Rule.Common.ApplyHyps
public meta import Iris.ProofMode.Aesop.Rule.Common.IExact
public meta import Iris.ProofMode.Aesop.Rule.Common.Identity
public meta import Iris.ProofMode.Aesop.Rule.Common.IPureIntro

public meta section

namespace Iris.ProofMode.Aesop

namespace RuleRunnerDescr

def run {Q : Type} [Queue Q] : RuleRunnerDescr → RuleRunner Q
  | .identity => Rule.Identity.run
  | .applyHyps => Rule.ApplyHyps.run
  | .iexact => Rule.IExact.run
  | .ipureIntro => Rule.IPureIntro.run
  | _ => λ _ => return {}

def replay : RuleRunnerDescr → RuleReplayer
  | .identity => Rule.Identity.replay
  | .applyHyps => Rule.ApplyHyps.replay
  | .iexact => Rule.IExact.replay
  | .ipureIntro => Rule.IPureIntro.replay
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

def commonIExactRuleId : RuleId where
  name := `iexact
  kind := .apply
  phase := .safe
  scope := .global

def commonIExactRule : Rule RuleInfo where
  id := commonIExactRuleId
  indexingMode := .unindexed
  info := RuleInfo.ofBuilder .iexact

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

def commonRuleIndex : Index RuleInfo :=
  ({} : Index RuleInfo)
    |>.add commonIdentityRule commonIdentityRule.indexingMode
    |>.add commonIExactRule commonIExactRule.indexingMode
    |>.add commonApplyHypsRule commonApplyHypsRule.indexingMode
    |>.add commonIPureIntroRule commonIPureIntroRule.indexingMode

end Iris.ProofMode.Aesop
