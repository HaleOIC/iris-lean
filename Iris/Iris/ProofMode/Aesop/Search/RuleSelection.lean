module

public meta import Iris.ProofMode.Aesop.Index.Query
public meta import Iris.ProofMode.Aesop.Rule.Baseline.Main
public meta import Iris.ProofMode.Aesop.Rule.Builtin.Main
public meta import Iris.ProofMode.Aesop.Search.SearchM

public meta section

namespace Iris.ProofMode.Aesop

open Lean.Meta

variable {Q : Type} [Queue Q]

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
  let config := (← readThe SearchM.Context).config
  let ruleIndex := if config.baseline? then baselineRuleIndex else builtinRuleIndex
  selectRulesFromIndex ruleIndex parentRef

end Iris.ProofMode.Aesop
