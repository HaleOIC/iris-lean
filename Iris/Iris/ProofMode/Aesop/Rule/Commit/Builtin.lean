module

public meta import Iris.ProofMode.Aesop.Search.SearchM
public meta import Iris.ProofMode.Aesop.Search.Types
public meta import Iris.ProofMode.Aesop.Rule.Types.Runner

public meta section

namespace Iris.ProofMode.Aesop.Rule.Commit.Builtin

open Lean Meta
open Iris.ProofMode.Aesop

variable {Q : Type} [Queue Q]

private def RappSpec.obunKind (spec : RappSpec) : ObunKind :=
  match spec.effect with
  | some (.contextManagement ..) => .managed
  | some (.closeGoal ..) | none => .plain

private def RappSpec.nodeState (spec : RappSpec) : NodeState :=
  if spec.goals.isEmpty then .proven else .unknown

private def getMVarDependenciesAtState
    (state : SavedState) (goal : MVarId) : SearchM Q (Std.HashSet MVarId) := do
  liftM (show MetaM _ from do
    restoreState state
    goal.getMVarDependencies)

def mkRappSpec (parentRef : GoalRef) (usedRule : Rule RuleInfo) (spec : RappSpec) :
    SearchM Q (RappRef × Array GoalRef) := do
  let parent ← parentRef.get
  let nodeState := RappSpec.nodeState spec
  let obunKind := RappSpec.obunKind spec
  let parentObun ← parent.parent.get
  let contextDepth :=
    if obunKind.isManaged then parentObun.contextDepth + 1
    else parentObun.contextDepth
  let successProbability := parent.successProbability * spec.successPossibility
  let obunRef ← IO.mkRef $ Obun.mk {
    id := ← getAndIncrementNextObunId
    parent? := none
    goals := #[]
    state := nodeState
    isIrrelevant := false
    scriptSteps? := none
    kind := obunKind
    contextDepth
    fullContextIrisSubgoals :=
      match spec.effect with
      | some effect => effect.fullContextIrisSubgoals
      | none => #[]
  }
  let rappRef ← IO.mkRef $ Rapp.mk {
    id := ← getAndIncrementNextRappId
    parent := parentRef
    children := obunRef
    state := nodeState
    isIrrelevant := false
    appliedRule := usedRule
    successProbability
    scriptSteps? := none
    usedHyp? :=
      match spec.effect with
      | some effect => effect.usedHyp?
      | none => none
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
      caseId := CaseId.ofIndex i
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
      unassignedMvars := ← getMVarDependenciesAtState spec.postState child.goal
      successProbability
      addedInIteration := currentIteration
      lastExpandedInIteration := currentIteration
      rulesQueue := {}
      appendiedGoalId := #[]
    }
  obunRef.modify fun o => (o.setParent rappRef).setGoals goalRefs
  return (rappRef, goalRefs)

end Iris.ProofMode.Aesop.Rule.Commit.Builtin
