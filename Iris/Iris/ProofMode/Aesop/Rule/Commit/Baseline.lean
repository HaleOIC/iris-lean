module

public meta import Iris.ProofMode.Aesop.Search.SearchM
public meta import Iris.ProofMode.Aesop.Search.Types
public meta import Iris.ProofMode.Aesop.Rule.Types.Runner

public meta section

namespace Iris.ProofMode.Aesop.Rule.Commit.Baseline

open Iris.ProofMode.Aesop

variable {Q : Type} [Queue Q]

private def RuleEffect.obunKind : RuleEffect → ObunKind
  | .contextManagement .. => .managed
  | .closeGoal .. => .plain

private def RappSpec.nodeState (spec : RappSpec) : NodeState :=
  if spec.goals.isEmpty then .proven else .unknown

def addRappSpec (parentRef : GoalRef) (spec : RappSpec) :
    SearchM Q (RappRef × Array GoalRef) := do
  let parent ← parentRef.get
  let nodeState := RappSpec.nodeState spec
  let successProbability := parent.successProbability * spec.successPossibility
  let obunRef ← IO.mkRef $ Obun.mk {
    id := ← getAndIncrementNextObunId
    parent? := none
    goals := #[]
    state := nodeState
    isIrrelevant := false
    metaState? := some spec.postState
    scriptSteps? := none
    kind := RuleEffect.obunKind spec.effect
  }
  let rappRef ← IO.mkRef $ Rapp.mk {
    id := ← getAndIncrementNextRappId
    parent := parentRef
    children := obunRef
    state := nodeState
    isIrrelevant := false
    appliedRule := RuleInfo.ofBuilder .custom
    successProbability
    scriptSteps? := none
    fullContextIrisSubgoals := spec.effect.fullContextIrisSubgoals
    consumedSpatialHyp? := spec.effect.consumedSpatialHyp?
    consumedLeanHyp? := none
    finalizedSpatialSplits := #[]
    metaState := spec.postState
    introducedMVars := {}
    assignedMVars := {}
  }
  let currentIteration ← getIteration
  let goalRefs ← spec.goals.mapIdxM fun i child => do
    IO.mkRef $ Goal.mk {
      id := ← getAndIncrementNextGoalId
      mask := (ProgressMask.empty spec.goals.size).mark i
      parent := obunRef
      children := #[]
      origin := .subgoal
      depth := parent.depth + 1
      state := .unknown
      isIrrelevant := false
      isForcedUnprovable := false
      preNormGoal := child.goal
      preNormState := spec.postState
      normalizationState := .notNormal
      unassignedMvars := ← child.goal.getMVarDependencies
      successProbability
      addedInIteration := currentIteration
      lastExpandedInIteration := currentIteration
      rulesQueue := {}
      appendiedGoalId := #[]
    }
  obunRef.modify fun o => (o.setParent rappRef).setGoals goalRefs
  return (rappRef, goalRefs)

end Iris.ProofMode.Aesop.Rule.Commit.Baseline
