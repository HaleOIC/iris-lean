module

public meta import Iris.ProofMode.Aesop.Index.Query
public meta import Iris.ProofMode.Aesop.Search.SearchM

public meta section

namespace Iris.ProofMode.Aesop

open Lean.Meta

variable {Q : Type} [Queue Q]

def selectRulesFromIndex (index : Index RuleInfo) (parentRef : GoalRef) :
    SearchM Q RuleQueue := do
  let parent ← parentRef.get
  let goal := parent.normalizationState.normalizedGoal?.getD parent.preNormGoal
  let state :=
    match parent.normalizationState with
    | .notNormal => parent.preNormState
    | .normal _ postState .. => postState
    | .provenByNorm postState .. => postState
  let results ← liftM do
    state.restore
    Index.queryMVar index goal
  for matchResult in results do
    if matchResult.rule.id.kind == .backward then
      trace[iaesop.search.expand] s!"iaesop.search.expand: matched backward decl {matchResult.rule.id.name}"
  return RuleQueue.ofArray results

def selectRules (parentRef : GoalRef) : SearchM Q RuleQueue := do
  let parent ← parentRef.get
  let ruleIndex := (← readThe SearchM.Context).ruleIndex
  if !parent.rulesQueue.isEmpty then
    return parent.rulesQueue
  selectRulesFromIndex ruleIndex parentRef

end Iris.ProofMode.Aesop
