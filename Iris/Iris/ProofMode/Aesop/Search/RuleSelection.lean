module

public meta import Iris.ProofMode.Aesop.Index.Query
public meta import Iris.ProofMode.Aesop.Search.SearchM

public meta section

namespace Iris.ProofMode.Aesop

open Lean.Meta

variable {Q : Type} [Queue Q]

-- [TODO]: Move this to rule folder associated with how to run the rules
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

def selectRulesFromIndex (index : Index RegularRule) (parentRef : GoalRef) :
    SearchM Q RuleQueue := do
  let parent ← parentRef.get
  let goal := parent.normalizationState.normalizedGoal?.getD parent.preNormGoal
  let state :=
    match parent.normalizationState with
    | .notNormal => parent.preNormState
    | .normal _ postState _ => postState
    | .provenByNorm postState _ => postState
  return RuleQueue.ofArray (← liftM do
    state.restore
    Index.queryMVar index goal)

def selectRules (parentRef : GoalRef) : SearchM Q RuleQueue := do
  let parent ← parentRef.get
  if !parent.rulesQueue.isEmpty then
    return parent.rulesQueue
  else
    selectRulesFromIndex builtinRuleIndex parentRef

end Iris.ProofMode.Aesop
