module

public meta import Iris.ProofMode.Aesop.Search.SearchM
public meta import Iris.ProofMode.Aesop.Search.Types
public meta import Iris.ProofMode.Aesop.Rule.Types.Runner

public meta section

namespace Iris.ProofMode.Aesop.Rule.Commit.Baseline

open Lean Meta
open Iris.ProofMode.Aesop

variable {Q : Type} [Queue Q]

private def RappSpec.nodeState (spec : RappSpec) : NodeState :=
  if spec.goals.isEmpty then .proven else .unknown

private def getMVarDependenciesAtState
    (state : SavedState) (goal : MVarId) : SearchM Q (Std.HashSet MVarId) := do
  liftM (show MetaM _ from do
    restoreState state
    goal.getMVarDependencies)

/- Make an initial rappRef for later modification -/
private def mkInitialRappRef (parentRef : GoalRef) (childRef : ObunRef)
    (usedRule : Rule RuleInfo) (postState : SavedState) : SearchM Q RappRef := do
  let parent ← parentRef.get
  let child ← childRef.get
  let ruleSuccessProb := usedRule.info.successProbability

  /- Collect new introduced metavariables from subgoals -/
  let introducedMVars ← child.goals.foldlM (init := {}) λ acc gref => do
    pure $ (← gref.get).unassignedMvars.fold (init := acc) λ acc mvarId =>
      if parent.unassignedMvars.contains mvarId then acc
      else acc.insert mvarId

  /- [TODO]: Collect assigned metavariables from subgoals -/
  IO.mkRef $ Rapp.mk {
    id := ← getAndIncrementNextRappId
    parent := parentRef
    children := childRef
    state := .unknown
    isIrrelevant := false
    appliedRule := usedRule
    successProbability := ruleSuccessProb * parent.successProbability
    metaState := postState

    /- The following context/script fields are filled by callers/finalization. -/
    usedHyp? := none
    scriptSteps? := none
    finalizedSpatialSplits := #[]
    introducedMVars
    assignedMVars := {}
  }

private structure PendingContextGoals where
  sourceObunId : ObunId
  goals : Array MVarId
  usedSpatialHyps : Array IrisHyp

private def removeUsedSpatialHypsFromGoal
    (irisGoal : IrisGoal) (usedSpatialHyps : Array IrisHyp) : MetaM IrisGoal :=
  usedSpatialHyps.foldlM (init := irisGoal) λ irisGoal usedHyp => do
    if !irisGoal.hyps.spatialIVarIds.contains usedHyp.ivar then
      throwError
        "iaesop: internal error: used Iris hypothesis is absent from pending goal context"
    let ⟨e', hyps', _, _, _, _, _⟩ :=
      irisGoal.hyps.remove false usedHyp.ivar
    return { irisGoal with e := e', hyps := hyps' }

private meta partial def collectPendingContextGoals
    (gref : GoalRef) : SearchM Q PendingContextGoals := do
  let g ← gref.get
  let parentObun ← g.parent.get
  /- Reached root, all determined, finished. -/
  if parentObun.id == .zero then
    return { sourceObunId := parentObun.id, goals := #[], usedSpatialHyps := #[] }

  if parentObun.kind.isPlain then
    if parentObun.goals.size > 1 then
      throwError s!"iaesop: plain obun {parentObun.id} has more than one subgoal; this case is not supported"
    let some rref := parentObun.parent?
      | throwError s!"iaesop: internal error: obun {parentObun.id} does not have parent"
    let rapp ← rref.get
    let here := rapp.usedHyp?.bind AppliedHyp.consumedSpatialHyp? |>.toArray
    let parentGoalRef := rapp.parent
    let pending ← collectPendingContextGoals parentGoalRef
    return {
      pending with
      usedSpatialHyps := here ++ pending.usedSpatialHyps
    }

  /- Non-plain obun, collect siblings context and goal -/
  let goals ← parentObun.goals.foldlM (init := #[]) λ acc otherRef => do
    let other ← otherRef.get
    if other.id != g.id && !other.isIrrelevant && !other.state.isProven then
      return acc.push (other.normalizationState.normalizedGoal?.getD other.preNormGoal)
    else
      return acc
  let sourceObunId :=
    match parentObun.kind with
    | .managed => parentObun.id
    | .inherited source => source
    | .plain => parentObun.id
  return { sourceObunId, goals, usedSpatialHyps := #[] }

/- Make an initial version ObunRef with its initial subgoals. -/
private def mkInitialObunRef (parentRef : GoalRef) (spec : RappSpec) :
    SearchM Q ObunRef := do
  let parent ← parentRef.get
  let state := RappSpec.nodeState spec
  let successProbability := parent.successProbability * spec.successPossibility
  let obunRef ← IO.mkRef $ Obun.mk {
    id := ← getAndIncrementNextObunId
    parent? := none
    goals := #[]
    state
    isIrrelevant := false
    scriptSteps? := none
    kind := .plain
    fullContextIrisSubgoals := #[]
  }
  let goalRefs ← spec.goals.mapIdxM λ idx child => do
    IO.mkRef $ Goal.mk {
      id := ← getAndIncrementNextGoalId
      mask := (ProgressMask.empty spec.goals.size).mark idx
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
      addedInIteration := ← getIteration
      lastExpandedInIteration := .zero
      rulesQueue := {}
      appendiedGoalId := #[]
    }
  obunRef.modify λ o => o.setGoals goalRefs
  return obunRef

/- Apply context management effect to the given obunRef -/
private def applyContextManagementEffect
    (obunRef : ObunRef) (irisSubgoals : Array IrisGoal) : SearchM Q Unit := do
  obunRef.modify λ o =>
    o.setKind .managed
     |>.setFullContextIrisSubgoals irisSubgoals

/- Apply close goal effect to the given obunRef -/
-- [TODO] One case has not been considered: what if consumedHyp has changed during the process?
-- [TODO] Another case: what if we are in nested context manage case? Recursively trace what happended before this finished context
private def applyCloseGoalEffect
    (parentRef : GoalRef) (obunRef : ObunRef)
    (spec : RappSpec) (usedHyp? : Option AppliedHyp) :
    SearchM Q Unit := do
  let obun ← obunRef.get
  if !obun.goals.isEmpty then
    throwError "iaesop: internal error: close-goal obun already has subgoals; inherited close-goal construction expects an empty obun"
  let pending ← collectPendingContextGoals parentRef
  let here := usedHyp?.bind AppliedHyp.consumedSpatialHyp? |>.toArray
  let pending := {
    pending with
    usedSpatialHyps := here ++ pending.usedSpatialHyps
  }
  if pending.goals.isEmpty then
    throwError
      "iaesop: close-goal inherited construction without pending goals is not supported yet"
  let parent ← parentRef.get
  let successProbability := parent.successProbability * spec.successPossibility
  let currentIteration ← getIteration
  let (pendingGoals, postState) ← liftM (show MetaM (Array (MVarId × Std.HashSet MVarId) × SavedState) from do
    restoreState spec.postState
    let pendingGoals ← pending.goals.mapM λ pendingGoal => do
      pendingGoal.withContext do
        let goalType ← instantiateMVars (← pendingGoal.getType)
        let some irisGoal := parseIrisGoal? goalType
          | throwError "iaesop: internal error: pending context goal is not an Iris goal"
        let irisGoal ← removeUsedSpatialHypsFromGoal irisGoal pending.usedSpatialHyps
        let goalExpr ← mkFreshExprSyntheticOpaqueMVar
          (IrisGoal.toExpr irisGoal) (← pendingGoal.getTag)
        let goal := goalExpr.mvarId!
        return (goal, ← goal.getMVarDependencies)
    return (pendingGoals, ← saveState))
  let goalRefs ← pendingGoals.mapIdxM λ idx (goal, unassignedMvars) => do
    IO.mkRef $ Goal.mk {
      id := ← getAndIncrementNextGoalId
      mask := (ProgressMask.empty pendingGoals.size).mark idx
      parent := obunRef
      children := #[]
      origin := .subgoal
      depth := parent.depth + 1
      state := .unknown
      isIrrelevant := false
      isForcedUnprovable := false
      preNormGoal := goal
      preNormState := postState
      normalizationState := .notNormal
      unassignedMvars
      successProbability
      addedInIteration := currentIteration
      lastExpandedInIteration := .zero
      rulesQueue := {}
      appendiedGoalId := #[]
    }
  obunRef.modify λ o =>
    o.setKind (.inherited pending.sourceObunId)
     |>.setGoals goalRefs

/- Make new rapp and goal according to the given RappSpec -/
def mkRappSpec (parentRef : GoalRef) (usedRule : Rule RuleInfo)
    (spec : RappSpec) : SearchM Q (RappRef × Array GoalRef) := do
  let obunRef ← mkInitialObunRef parentRef spec
  match spec.effect with
  | some (.contextManagement irisSubgoals ..) =>
    applyContextManagementEffect obunRef irisSubgoals
  | some (.closeGoal usedHyp?) =>
    applyCloseGoalEffect parentRef obunRef spec usedHyp?
  | none => pure ()
  let rappRef ← mkInitialRappRef parentRef obunRef usedRule spec.postState
  rappRef.modify λ r =>
    r.setUsedHyp? <| spec.effect.bind RuleEffect.usedHyp?
  obunRef.modify λ o => o.setParent rappRef
  let goalRefs := (← obunRef.get).goals
  return (rappRef, goalRefs)

end Iris.ProofMode.Aesop.Rule.Commit.Baseline
