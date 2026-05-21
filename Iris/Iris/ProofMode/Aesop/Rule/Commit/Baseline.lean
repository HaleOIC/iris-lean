module

public meta import Iris.ProofMode.Aesop.Search.SearchM
public meta import Iris.ProofMode.Aesop.Search.Types
public meta import Iris.ProofMode.Aesop.Rule.Types.Runner

public meta section

namespace Iris.ProofMode.Aesop.Baseline

open Lean Meta
open Iris.ProofMode.Aesop

variable {Q : Type} [Queue Q]

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
    introducedMVars
    assignedMVars := {}
  }

/- Pending information during the collection procedure -/
private structure PendingContextGoals where
  sourceObunId : ObunId
  sourceObunDepth : Nat
  leftIrisGoals : Array (CaseId × IrisGoal)
  usedSpatialHyps : Array IrisHyp
  deriving Inhabited

private def PendingContextGoals.empty  : PendingContextGoals := {
  sourceObunId := .zero
  sourceObunDepth := 0
  leftIrisGoals := #[]
  usedSpatialHyps := #[]
}

/- Recursively collect pending information -/
private meta partial def collectPendingContextGoals (gref : GoalRef)
    (skip? : Option ObunId) : SearchM Q PendingContextGoals := do
  let g ← gref.get
  let parentObun ← g.parent.get
  /- Reached root, all determined, finished. -/
  if parentObun.id == .zero then return .empty

  /- Skip the solved context manage obun -/
  if let some source := skip? then
    match parentObun.kind with
    | .inherited source' =>
      if source' == source then
        let some rref := parentObun.parent?
          | throwError s!"iaesop(baseline): obun {parentObun.id} does not have parent"
        let rapp ← rref.get
        return ← collectPendingContextGoals rapp.parent skip?
    | .managed =>
      if parentObun.id == source then
        let some rref := parentObun.parent?
          | throwError s!"iaesop(baseline): obun {parentObun.id} does not have parent"
        let rapp ← rref.get
        return ← collectPendingContextGoals rapp.parent none
    | .plain =>
      pure ()

  /- Plain obun: collect its parent rapp's used spatial hypothesis. -/
  if parentObun.kind.isPlain then
    if parentObun.goals.size > 1 then
      throwError s!"iaesop(baseline): plain obun {parentObun.id} has more than one subgoal; this case is not supported"
    let some rref := parentObun.parent?
      | throwError s!"iaesop(baseline): obun {parentObun.id} does not have parent"
    let rapp ← rref.get
    let here := rapp.usedHyp?.bind (·.consumedSpatialHyp?) |>.toArray
    let parentGoalRef := rapp.parent
    let pending ← collectPendingContextGoals parentGoalRef skip?
    return { pending with usedSpatialHyps := here ++ pending.usedSpatialHyps }

  /- Non-plain obun: collect siblings context and IrisGoal(template) -/
  let (_, leftIrisGoals) ← parentObun.goals.foldlM (init := (0, #[])) λ (idx, acc) otherRef => do
    let other ← otherRef.get
    let some irisGoal := parentObun.fullContextIrisSubgoals[idx]?
      | throwError s!"iaesop(baseline): missing full-context iris subgoal at index {idx}"
    let some caseId := other.caseId?
      | throwError s!"iaesop(baseline): copied sibling does not have caseId"
    -- [TODO]: Not sure whether we should check the sibling's state is irrelevant or proven
    let acc := if other.id != g.id then acc.push (caseId, irisGoal) else acc
    return (idx + 1, acc)

  /- Start to skip the already managed obun covering range -/
  if leftIrisGoals.isEmpty then
    let some rref := parentObun.parent?
      | throwError s!"iaesop(baseline): obun {parentObun.id} does not have parent"
    let rapp ← rref.get
    match parentObun.kind with
    | .inherited source => return ← collectPendingContextGoals rapp.parent (some source)
    | .managed => throwError "iaesop(baseline): managed obun branch should not be reached when collecting pending goals"
    | .plain => throwError "iaesop(baseline): plain obun branch should not be reached when collecting pending goals"

  /- Otherwise, return current pending info -/
  let (sourceObunId, sourceObunDepth) ← match parentObun.kind with
    | .managed => pure (parentObun.id, parentObun.contextDepth)
    | .inherited source => pure (source, parentObun.contextDepth)
    | .plain => throwError "iaesop(baseline): plain obun branch should not be reached when collecting pending goals"
  return { sourceObunId, sourceObunDepth, leftIrisGoals, usedSpatialHyps := #[] }

/- Make an initial version ObunRef with its initial subgoals. -/
private def mkInitialObunRef (parentRef : GoalRef) (spec : RappSpec) :
    SearchM Q ObunRef := do
  let parent ← parentRef.get
  let obunRef ← IO.mkRef $ Obun.mk {
    id := ← getAndIncrementNextObunId
    parent? := none -- Filled in later
    goals := #[] -- Filled in later
    state := .unknown
    isIrrelevant := false
    kind := .plain
    contextDepth := (← parent.parent.get).contextDepth
    fullContextIrisSubgoals := #[]
    finalizedSpatialSplits := #[]
    scriptSteps? := none
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
      successProbability := parent.successProbability * spec.successPossibility
      addedInIteration := ← getIteration
      lastExpandedInIteration := .zero
      rulesQueue := {}
      appendiedGoalId := #[]  -- Not used in baseline
      caseId? := none
    }
  obunRef.modify λ o => o.setGoals goalRefs
  return obunRef

/- Apply context management effect to the given obunRef -/
private def applyContextManagementEffect (obunRef : ObunRef)
    (irisSubgoals : Array IrisGoal) : SearchM Q Unit := do
  -- Single subgoal does not need context management
  if irisSubgoals.size == 1 then return

  let obun ← obunRef.get
  if obun.goals.size != irisSubgoals.size then
    throwError s!"iaesop(baseline): context management has {irisSubgoals.size} templates but {obun.goals.size} goals"
  let _ ← obun.goals.foldlM (init := 0) λ idx gref => do
    gref.modify λ g => g.setCaseId (CaseId.ofNat idx)
    return idx + 1
  obunRef.modify λ o =>
    o.setKind .managed
     |>.setContextDepth (o.contextDepth + 1)
     |>.setFullContextIrisSubgoals irisSubgoals

/- Helper function: remove usedSpatialHyps from given irisGoal template -/
private def removeUsedSpatialHypsFromGoal
    (irisGoal : IrisGoal) (usedSpatialHyps : Array IrisHyp) : MetaM IrisGoal :=
  usedSpatialHyps.foldlM (init := irisGoal) λ irisGoal usedHyp => do
    if !irisGoal.hyps.spatialIVarIds.contains usedHyp.ivar then
      return irisGoal
    let ⟨e', hyps', _, _, _, _, _⟩ :=
      irisGoal.hyps.remove false usedHyp.ivar
    return { irisGoal with e := e', hyps := hyps' }

/- Apply close goal effect to the given obunRef -/
private def applyCloseGoalEffect (parentRef : GoalRef) (obunRef : ObunRef)
    (spec : RappSpec) (usedHyp? : Option AppliedHyp) : SearchM Q Unit := do
  let obun ← obunRef.get
  if !obun.goals.isEmpty then throwError "iaesop(baseline): close-goal obun still has subgoals"

  /- Collect pending information from above tree, ready for copying siblings as new subgoals -/
  let pending ← collectPendingContextGoals parentRef none
  let here := usedHyp?.bind AppliedHyp.consumedSpatialHyp? |>.toArray
  let pending := { pending with usedSpatialHyps := here ++ pending.usedSpatialHyps }
  if pending.leftIrisGoals.isEmpty then
    obunRef.modify λ o =>
      o.setKind (.inherited pending.sourceObunId)
        |>.setContextDepth pending.sourceObunDepth
        |>.setFullContextIrisSubgoals #[]
        |>.setState .proven
    return

  /- Fabricate the new goals with removed context in the current goal context. -/
  let parent ← parentRef.get
  let (pendingGoals, postState) ←
      liftM (show MetaM (Array (CaseId × IrisGoal × MVarId × Std.HashSet MVarId) × SavedState) from do
    restoreState spec.postState
    let tag ← parent.preNormGoal.getTag
    let pendingGoals ← pending.leftIrisGoals.mapM λ (caseId, pendingGoal) => do
      let irisGoal ← removeUsedSpatialHypsFromGoal pendingGoal pending.usedSpatialHyps
      let goalExpr ← mkFreshExprSyntheticOpaqueMVar (IrisGoal.toExpr irisGoal) tag
      let goal := goalExpr.mvarId!
      return (caseId, irisGoal, goal, ← goal.getMVarDependencies)
    return (pendingGoals, ← saveState))
  let irisSubgoals := pendingGoals.map λ (_, irisGoal, _, _) => irisGoal
  let goalRefs ← pendingGoals.mapIdxM λ idx (caseId, _, goal, unassignedMvars) => do
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
      successProbability := parent.successProbability * spec.successPossibility
      addedInIteration := ← getIteration
      lastExpandedInIteration := .zero
      rulesQueue := {}
      appendiedGoalId := #[]
      caseId? := some caseId
    }
  /- Inherited obun also preserve the irisSubgoals template -/
  obunRef.modify λ o =>
    o.setKind (.inherited pending.sourceObunId)
      |>.setContextDepth pending.sourceObunDepth
      |>.setFullContextIrisSubgoals irisSubgoals
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

  /- Record the used hypothesis in the rapp node -/
  rappRef.modify λ r =>
    r.setUsedHyp? <| spec.effect.bind RuleEffect.usedHyp?
  obunRef.modify λ o => o.setParent rappRef
  if (← obunRef.get).state.isProven then
    rappRef.modify λ r => r.setState .proven
  let goalRefs := (← obunRef.get).goals
  return (rappRef, goalRefs)

end Iris.ProofMode.Aesop.Baseline
