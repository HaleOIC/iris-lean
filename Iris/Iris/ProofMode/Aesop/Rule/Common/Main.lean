module

public meta import Iris.ProofMode.Aesop.Index.Query
public meta import Iris.ProofMode.Aesop.Rule.Common.IExact
public meta import Iris.ProofMode.Aesop.Rule.Common.Identity

public meta section

namespace Iris.ProofMode.Aesop

namespace RuleRunnerDescr

def run {Q : Type} [Queue Q] : RuleRunnerDescr → RuleRunner Q
  | .identity => Rule.Identity.run
  | .iexact => Rule.IExact.run
  | _ => fun _ => return {}

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

def commonRuleIndex : Index RuleInfo :=
  ({} : Index RuleInfo)
    |>.add commonIdentityRule commonIdentityRule.indexingMode
    |>.add commonIExactRule commonIExactRule.indexingMode

end Iris.ProofMode.Aesop
