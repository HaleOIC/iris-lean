module

public meta import Iris.ProofMode.Aesop.Index.Query
public meta import Iris.ProofMode.Aesop.Search.SearchM

public meta section

namespace Iris.ProofMode.Aesop

open Lean.Meta

variable {Q : Type} [Queue Q]

private def isErasedTheoremRule (erasedRules : Array ErasedTheoremRule)
    (rule : Rule RuleInfo) : Bool :=
  erasedRules.any λ erased =>
    erased.kind == rule.id.kind && erased.decl == rule.id.name

def selectRulesFromIndex (index : Index RuleInfo) (parentRef : GoalRef) :
    SearchM Q RuleQueue := do
  let parent ← parentRef.get
  let goal := parent.normalizationState.normalizedGoal?.getD parent.preNormGoal
  let state :=
    match parent.normalizationState with
    | .notNormal => parent.preNormState
    | .normal _ postState .. => postState
    | .provenByNorm postState .. => postState
  let erasedTheoremRules := (← readThe SearchM.Context).config.erasedTheoremRules
  let results ← liftM do
    state.restore
    Index.queryMVar index goal λ rule =>
      !isErasedTheoremRule erasedTheoremRules rule
  return RuleQueue.ofArray results

def selectRules (parentRef : GoalRef) : SearchM Q RuleQueue := do
  let parent ← parentRef.get
  let ruleIndex := (← readThe SearchM.Context).ruleIndex
  if !parent.rulesQueue.isEmpty then
    return parent.rulesQueue
  selectRulesFromIndex ruleIndex parentRef

end Iris.ProofMode.Aesop
