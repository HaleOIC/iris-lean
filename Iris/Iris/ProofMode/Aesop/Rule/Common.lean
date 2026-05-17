module

public meta import Iris.ProofMode.Aesop.Search.SearchM
public meta import Iris.ProofMode.Aesop.Search.Types
public meta import Iris.ProofMode.Aesop.Rule.Types.Runner

public meta section

namespace Iris.ProofMode.Aesop

open Lean Meta Std

variable {Q : Type} [Queue Q]

def normalizedGoalAndState (ruleName : String) (parent : Goal) :
    SearchM Q (MVarId × SavedState) := do
  match parent.normalizationState with
  | .normal postGoal postState .. =>
    return (postGoal, postState)
  | .provenByNorm .. =>
    throwError "iaesop: internal error: {ruleName} ran on a goal already proven by normalization"
  | .notNormal =>
    throwError "iaesop: internal error: {ruleName} ran on a non-normalized goal"

def mkChildGoalSpec (goal : MVarId) : MetaM ChildGoalSpec := do
  goal.withContext do
    let goalType ← instantiateMVars (← goal.getType)
    let some irisGoal := Iris.ProofMode.parseIrisGoal? goalType
      | throwError "iaesop: internal error: generated child goal is not an Iris goal"
    return {
      goal
      irisGoal
      mvars := ← goal.getMVarDependencies
    }

partial def findManagedObun? (gref : GoalRef) :
    SearchM Q (Option ObunRef) := do
  let g ← gref.get
  let obunRef := g.parent
  let obun ← obunRef.get
  if obun.kind.isManaged && obun.state.isUnknown then
    return some obunRef
  else
    match obun.parent? with
    | none => return none
    | some rappRef =>
      findManagedObun? (← rappRef.get).parent

def mkRuleInput (ruleName : String) (parentRef : GoalRef)
    (matchResult : RuleMatch) : SearchM Q (Option RuleInput) := do
  let parent ← parentRef.get
  let some goal := parent.normalizationState.normalizedGoal?
    | return none
  let (_, state) ← normalizedGoalAndState ruleName parent
  let managedObun? ← findManagedObun? parentRef
  let managedState? : Option SavedState ←
    match managedObun? with
    | none => pure (none : Option SavedState)
    | some obunRef => pure (← obunRef.get).metaState?
  return some {
    parentRef
    parent
    matchResult
    goal
    state
    managedObun?
    managedState?
  }

private def addRappSpec
    (parentRef : GoalRef) (parent : Goal) (matchResult : RuleMatch)
    (spec : RappSpec) :
    SearchM Q (RappRef × Array GoalRef) := do
  let successProbability :=
    parent.successProbability * matchResult.rule.info.successProbability
  let obunRef ← IO.mkRef $ Obun.mk {
    id := ← getAndIncrementNextObunId
    parent? := none
    goals := #[]
    state := spec.obunState
    isIrrelevant := false
    metaState? := some spec.metaState
    scriptSteps? := none
    kind := spec.obunKind
  }
  let rappRef ← IO.mkRef $ Rapp.mk {
    id := ← getAndIncrementNextRappId
    parent := parentRef
    children := obunRef
    state := spec.rappState
    isIrrelevant := false
    appliedRule := matchResult.rule.info
    successProbability
    scriptSteps? := none
    fullContextIrisSubgoals := spec.fullContextIrisSubgoals
    consumedSpatialHyp? := spec.consumedSpatialHyp?
    consumedLeanHyp? := spec.consumedLeanHyp?
    finalizedSpatialSplits := spec.finalizedSpatialSplits
    metaState := spec.metaState
    introducedMVars := spec.introducedMVars
    assignedMVars := spec.assignedMVars
  }
  let currentIteration ← getIteration
  let goalRefs ← spec.childGoals.mapIdxM λ i child => do
    IO.mkRef $ Goal.mk {
      id := ← getAndIncrementNextGoalId
      mask := (ProgressMask.empty spec.childGoals.size).mark i
      parent := obunRef
      children := #[]
      origin := .subgoal
      depth := parent.depth + 1
      state := .unknown
      isIrrelevant := false
      isForcedUnprovable := false
      preNormGoal := child.goal
      preNormState := spec.metaState
      normalizationState := .notNormal
      unassignedMvars := child.mvars
      successProbability
      addedInIteration := currentIteration
      lastExpandedInIteration := currentIteration
      rulesQueue := {}
      appendiedGoalId := #[]
    }
  obunRef.modify λ o => (o.setParent rappRef).setGoals goalRefs
  return (rappRef, goalRefs)

def addRappSpecs (parentRef : GoalRef) (matchResult : RuleMatch)
    (specs : Array RappSpec) : SearchM Q RuleResult := do
  if specs.isEmpty then
    return .failed
  let parent ← parentRef.get
  let mut rappRefs := #[]
  let mut goalsToEnqueue := #[]
  for spec in specs do
    let (rappRef, goalRefs) ← addRappSpec parentRef parent matchResult spec
    rappRefs := rappRefs.push rappRef
    goalsToEnqueue := goalsToEnqueue ++ goalRefs
  let parentState? :=
    specs.foldl (init := (none : Option GoalState)) λ state? spec =>
      match state? with
      | some state => some state
      | none => spec.parentState?
  parentRef.modify λ g =>
    let g := g.setChildren (g.children ++ rappRefs)
    match parentState? with
    | some state => g.setState state
    | none => g
  enqueueGoals goalsToEnqueue
  if specs.any (·.parentState?.isSome) then
    return .proved rappRefs
  else
    return .succeeded rappRefs

private def applyRuleEffectSideEffects (input : RuleInput)
    (effect : RuleEffect) : SearchM Q Unit := do
  match input.managedObun?, effect.managedObunPostState? with
  | some obunRef, some postState =>
    obunRef.modify λ o => o.setMetaState? (some postState)
  | _, _ =>
    return ()

def addRuleOutput (input : RuleInput) (output : RuleOutput) :
    SearchM Q RuleResult := do
  for effect in output.ruleEffects do
    applyRuleEffectSideEffects input effect
  addRappSpecs input.parentRef input.matchResult
    (output.ruleEffects.map (·.rappSpec))

end Iris.ProofMode.Aesop
