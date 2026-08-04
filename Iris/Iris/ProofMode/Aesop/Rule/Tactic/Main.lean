module

public meta import Iris.ProofMode.Aesop.Index.Query
public meta import Iris.ProofMode.Aesop.Rule.Tactic.ApplyHyps
public meta import Iris.ProofMode.Aesop.Rule.Tactic.HaveHyps
public meta import Iris.ProofMode.Aesop.Rule.Tactic.ICases
public meta import Iris.ProofMode.Aesop.Rule.Tactic.Identity
public meta import Iris.ProofMode.Aesop.Rule.Tactic.IMod
public meta import Iris.ProofMode.Aesop.Rule.Tactic.IModIntro
public meta import Iris.ProofMode.Aesop.Rule.Tactic.IPureIntro
public meta import Iris.ProofMode.Aesop.Rule.Tactic.ILeftRight
public meta import Iris.ProofMode.Aesop.Rule.Tactic.IExist
public meta import Iris.ProofMode.Aesop.Rule.Tactic.ISplit

public meta section

namespace Iris.ProofMode.Aesop

namespace TacticDescr

def run {Q : Type} [Queue Q] : TacticDescr → RuleRunner Q
  | .identity => Rule.Identity.run
  | .applyHyps => Rule.ApplyHyps.run
  | .haveHyps => Rule.HaveHyps.run
  | .icases => Rule.ICases.run
  | .icasesFalse => Rule.ICases.runFalse
  | .imod => Rule.IMod.run
  | .imodIntro => Rule.IModIntro.run
  | .ipureIntro => Rule.IPureIntro.run
  | .ileft => Rule.ILeftRight.runLeft
  | .iright => Rule.ILeftRight.runRight
  | .iexist => Rule.IExist.run
  | .isplit => Rule.ISplit.run
  | _ => λ _ => return {}

def replay : TacticDescr → RuleReplayer
  | .identity => Rule.Identity.replay
  | .applyHyps => Rule.ApplyHyps.replay
  | .haveHyps => Rule.HaveHyps.replay
  | .icases => Rule.ICases.replay
  | .icasesFalse => Rule.ICases.replayFalse
  | .imod => Rule.IMod.replay
  | .imodIntro => Rule.IModIntro.replay
  | .ipureIntro => Rule.IPureIntro.replay
  | .ileft => Rule.ILeftRight.replayLeft
  | .iright => Rule.ILeftRight.replayRight
  | .iexist => Rule.IExist.replay
  | .isplit => Rule.ISplit.replay
  | _ => λ input => return #[input.goal]

end TacticDescr

def commonIdentityRuleId : RuleId where
  name := `identity
  kind := .forward
  phase := .safe
  scope := .global

def commonIdentityRule : Rule RuleInfo where
  id := commonIdentityRuleId
  indexingMode := .unindexed
  info := RuleInfo.ofBuilder (.tactic .identity) .almost

def commonApplyHypsRuleId : RuleId where
  name := `applyHyps
  kind := .apply
  phase := .safe
  scope := .global

def commonApplyHypsRule : Rule RuleInfo where
  id := commonApplyHypsRuleId
  indexingMode := .unindexed
  info := RuleInfo.ofBuilder (.tactic .applyHyps) .high

def commonHaveHypsRuleId : RuleId where
  name := `haveHyps
  kind := .forward
  phase := .safe
  scope := .global

def commonHaveHypsRule : Rule RuleInfo where
  id := commonHaveHypsRuleId
  indexingMode := .unindexed
  info := RuleInfo.ofBuilder (.tactic .haveHyps) .almost

def commonICasesRuleId : RuleId where
  name := `icases
  kind := .forward
  phase := .safe
  scope := .global

def commonICasesRule : Rule RuleInfo where
  id := commonICasesRuleId
  indexingMode := .unindexed
  info := RuleInfo.ofBuilder (.tactic .icases) .almost

def commonICasesFalseRuleId : RuleId where
  name := `icasesFalse
  kind := .forward
  phase := .safe
  scope := .global

def commonICasesFalseRule : Rule RuleInfo where
  id := commonICasesFalseRuleId
  indexingMode := .unindexed
  info := RuleInfo.ofBuilder (.tactic .icasesFalse) ⟨0.1⟩

def commonIPureIntroRuleId : RuleId where
  name := `ipureIntro
  kind := .apply
  phase := .safe
  scope := .global

def commonIPureIntroRule : Rule RuleInfo where
  id := commonIPureIntroRuleId
  indexingMode := .unindexed
  info := RuleInfo.ofBuilder (.tactic .ipureIntro) .high

def commonIExistRuleId : RuleId where
  name := `iExist
  kind := .apply
  phase := .safe
  scope := .global

def commonIExistRule : Rule RuleInfo where
  id := commonIExistRuleId
  indexingMode := .unindexed
  info := RuleInfo.ofBuilder (.tactic .iexist) .almost

def commonILeftRuleId : RuleId where
  name := `ileft
  kind := .apply
  phase := .safe
  scope := .global

def commonILeftRule : Rule RuleInfo where
  id := commonILeftRuleId
  indexingMode := .unindexed
  info := RuleInfo.ofBuilder (.tactic .ileft) .high

def commonIRightRuleId : RuleId where
  name := `iright
  kind := .apply
  phase := .safe
  scope := .global

def commonIRightRule : Rule RuleInfo where
  id := commonIRightRuleId
  indexingMode := .unindexed
  info := RuleInfo.ofBuilder (.tactic .iright) .high

def commonIModIntroRuleId : RuleId where
  name := `imodintro
  kind := .apply
  phase := .safe
  scope := .global

def commonIModIntroRule : Rule RuleInfo where
  id := commonIModIntroRuleId
  indexingMode := .unindexed
  info := RuleInfo.ofBuilder (.tactic .imodIntro) .medium

def commonIModRuleId : RuleId where
  name := `imod
  kind := .apply
  phase := .safe
  scope := .global

def commonIModRule : Rule RuleInfo where
  id := commonIModRuleId
  indexingMode := .unindexed
  info := RuleInfo.ofBuilder (.tactic .imod) .high

def commonISplitRuleId : RuleId where
  name := `isplit
  kind := .apply
  phase := .safe
  scope := .global

def commonISplitRule : Rule RuleInfo where
  id := commonISplitRuleId
  indexingMode := .unindexed
  info := RuleInfo.ofBuilder (.tactic .isplit) .almost

def commonRuleIndex : Index RuleInfo :=
  ({} : Index RuleInfo)
    |>.add commonIdentityRule commonIdentityRule.indexingMode
    |>.add commonApplyHypsRule commonApplyHypsRule.indexingMode
    |>.add commonHaveHypsRule commonHaveHypsRule.indexingMode
    |>.add commonICasesRule commonICasesRule.indexingMode
    |>.add commonICasesFalseRule commonICasesFalseRule.indexingMode
    |>.add commonIModRule commonIModRule.indexingMode
    |>.add commonIPureIntroRule commonIPureIntroRule.indexingMode
    |>.add commonIExistRule commonIExistRule.indexingMode
    |>.add commonILeftRule commonILeftRule.indexingMode
    |>.add commonIRightRule commonIRightRule.indexingMode
    |>.add commonIModIntroRule commonIModIntroRule.indexingMode
    |>.add commonISplitRule commonISplitRule.indexingMode

end Iris.ProofMode.Aesop
