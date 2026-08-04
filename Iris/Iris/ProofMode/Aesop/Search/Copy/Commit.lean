module

public meta import Iris.ProofMode.Aesop.Search.Shared.CoreM
public meta import Iris.ProofMode.Aesop.Search.Shared.Types
public meta import Iris.ProofMode.Aesop.Rule.Types.Runner
public meta import Iris.ProofMode.Aesop.Search.Copy.Settlement

public meta section

namespace Iris.ProofMode.Aesop.Search.Copy

open Lean Meta
open Iris.ProofMode.Aesop

variable {Q : Type} [Queue Q]

private def getMVarDependenciesAtState
    (state : SavedState) (goal : MVarId) : CoreM Q (Std.HashSet MVarId) := do
  liftM (show MetaM _ from do
    restoreState state
    goal.getMVarDependencies)

/- Make an initial rappRef for later modification -/
private def mkInitialRappRef (parentRef : GoalRef) (childRef : ObunRef)
    (usedRule : Rule RuleInfo) (postState : SavedState) : CoreM Q RappRef := do
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
    usedHyps := #[]
    generatedSpatialHyps := #[]
    scriptSteps? := none
    introducedMVars
    assignedMVars := {}
  }

/- Pending information during the collection procedure -/
private structure PendingContextGoals where
  sourceObunId : ObunId
  sourceObunDepth : Nat
  sourceObunKind : ObunKind
  leftIrisGoals : Array (CaseId × IrisGoal × GoalRef)
  involvedHyps : Array Hyp
  deriving Inhabited

/- Recursively collect pending information -/
private meta partial def collectPendingContextGoals (gref : GoalRef)
    (skip? : Option ObunId) : CoreM Q PendingContextGoals := do
  let g ← gref.get
  let parentObun ← g.parent.get

  /- Hyp comes from two cases: normalization or rule application -/
  let goalHyps :=
    g.normalizationState.generatedSpatialHyps.map Hyp.generated ++
    g.normalizationState.usedSpatialHyps.map Hyp.consumed

  /- Reached root, all determined, finished. -/
  if parentObun.id == .zero then
    let pending : PendingContextGoals := default
    return { pending with involvedHyps := goalHyps }

  let some rref := parentObun.parent?
      | throwError s!"iaesop(copy): obun {parentObun.id} does not have parent"
  let rapp ← rref.get
  let rappHyps :=
    rapp.generatedSpatialHyps.map Hyp.generated ++
    rapp.consumedSpatialHyps.map Hyp.consumed

  /- Check the skip? -/
  match skip? with
  | none => match parentObun.kind with
    | .managed | .duplicated | .inherited .. =>
      let (_, leftIrisGoals) ← parentObun.goals.foldlM (init := (0, #[])) λ (idx, acc) otherRef => do
        let other ← otherRef.get
        let some irisGoal := parentObun.fullContextIrisSubgoals[idx]?
          | throwError s!"iaesop(copy): missing full-context iris subgoal at index {idx}"
        let some caseId := other.caseId?
          | throwError s!"iaesop(copy): copied sibling does not have caseId"
        -- [TODO]: Not sure whether we should check the sibling's state is irrelevant or proven
        let acc := if other.id != g.id then acc.push (caseId, irisGoal, otherRef) else acc
        return (idx + 1, acc)
      if leftIrisGoals.isEmpty then
        let nextSkip? := parentObun.kind.source?
        let pending ← collectPendingContextGoals rapp.parent nextSkip?
        return { pending with involvedHyps := goalHyps ++ rappHyps ++ pending.involvedHyps }
      else
        let (sourceObunId, sourceObunDepth) ← match parentObun.kind with
          | .managed => pure (parentObun.id, parentObun.contextDepth)
          | .duplicated => pure (parentObun.id, parentObun.contextDepth)
          | .inherited source _ => pure (source, parentObun.contextDepth)
          | .plain => throwError "iaesop(copy): plain obun branch should not be reached when collecting pending goals"
        return { sourceObunId, sourceObunDepth, sourceObunKind := parentObun.kind, leftIrisGoals, involvedHyps := goalHyps }
    | .plain =>
      if parentObun.goals.size > 1 then
        throwError s!"iaesop(copy): plain obun {parentObun.id} has more than one subgoal; this case is not supported"
      let pending ← collectPendingContextGoals rapp.parent skip?
      return { pending with involvedHyps := goalHyps ++ rappHyps ++ pending.involvedHyps }
  | some source =>
    let doneSkipping := (parentObun.kind.isManaged || parentObun.kind.isDuplicated) && parentObun.id == source
    let pending ← collectPendingContextGoals rapp.parent <| if doneSkipping then none else skip?
    return { pending with involvedHyps := goalHyps ++ rappHyps ++ pending.involvedHyps }

/- Make an initial version ObunRef with its initial subgoals. -/
private def mkInitialObunRef (parentRef : GoalRef) (spec : RappSpec) :
    CoreM Q ObunRef := do
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
      appendiedGoalId := #[]  -- Not used in copy search
      caseId? := none
    }
  obunRef.modify λ o => o.setGoals goalRefs
  return obunRef

/- Apply multiple goal effect to the given obunRef -/
private def applyMultipleGoalsEffect (obunRef : ObunRef)
    (irisSubgoals : Array IrisGoal) : CoreM Q Unit := do
  if irisSubgoals.size <= 1 then
    throwError "iaesop(copy): multiple subgoal effect must have more than one subgoals"

  let obun ← obunRef.get
  if obun.goals.size != irisSubgoals.size then
    throwError s!"iaesop(copy): multiple subgoal effect has {irisSubgoals.size} templates but {obun.goals.size} goals"
  let _ ← obun.goals.foldlM (init := 0) λ idx gref => do
    gref.modify λ g => g.setCaseId (CaseId.ofNat idx)
    return idx + 1
  obunRef.modify λ o =>
    o.setKind .duplicated
     |>.setContextDepth (o.contextDepth + 1)
     |>.setFullContextIrisSubgoals irisSubgoals

/- Apply context management effect to the given obunRef -/
private def applyContextManagementEffect (obunRef : ObunRef)
    (irisSubgoals : Array IrisGoal) : CoreM Q Unit := do
  -- Single subgoal does not need context management
  if irisSubgoals.size <= 1 then
    throwError "iaesop(copy): context management must have more than one templates"

  let obun ← obunRef.get
  if obun.goals.size != irisSubgoals.size then
    throwError s!"iaesop(copy): context management has {irisSubgoals.size} templates but {obun.goals.size} goals"
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
    (spec : RappSpec) : CoreM Q Unit := do
  let obun ← obunRef.get
  if !obun.goals.isEmpty then throwError "iaesop(copy): close-goal obun still has subgoals"

  /- Collect pending information from above tree, ready for copying siblings as new subgoals -/
  let pending ← collectPendingContextGoals parentRef none
  let effectHyps :=
    spec.effect.generatedSpatialHyps.map Hyp.generated ++
    (spec.effect.usedHyps.filterMap AppliedHyp.consumedSpatialHyp?).map Hyp.consumed
  let pending := { pending with involvedHyps := effectHyps ++ pending.involvedHyps }
  let usedSpatialHyps := netConsumedHyps pending.involvedHyps
  if pending.leftIrisGoals.isEmpty then
    obunRef.modify λ o =>
      o.setKind (.inherited pending.sourceObunId true)
        |>.setContextDepth pending.sourceObunDepth
        |>.setFullContextIrisSubgoals #[]
        |>.setState .proven
    return

  /- Fabricate the new goals with removed context in the current goal context. -/
  let parent ← parentRef.get
  let (pendingGoals, postState) ←
      liftM (show MetaM (Array (CaseId × IrisGoal × MVarId × Std.HashSet MVarId) × SavedState) from do
    spec.postState.restore
    let tag ← parent.preNormGoal.getTag
    let pendingGoals ← pending.leftIrisGoals.mapM λ (caseId, pendingGoal, sourceRef) => do
      let source ← sourceRef.get
      match pending.sourceObunKind with
      | .managed | .inherited _ true =>
        let irisGoal ← removeUsedSpatialHypsFromGoal pendingGoal usedSpatialHyps
        let goal ← source.preNormGoal.withContext do
          let goalExpr ← mkFreshExprSyntheticOpaqueMVar (IrisGoal.toExpr irisGoal) tag
          return goalExpr.mvarId!
        return (caseId, irisGoal, goal, ← goal.getMVarDependencies)
      | .duplicated | .inherited _ false =>
        return (caseId, pendingGoal, source.preNormGoal, ← source.preNormGoal.getMVarDependencies)
      | _ => throwError "iaesop(copy): this branch should not be reached during construction of pending goals"
    return (pendingGoals, ← saveState))
  let irisSubgoals := pendingGoals.map λ (_, irisGoal, _, _) => irisGoal
  let goalRefs ← pendingGoals.mapIdxM λ idx (caseId, _, goal, unassignedMvars) => do
    let newGoalId ← getAndIncrementNextGoalId
    trace[iaesop.tactic] s!"iaesop.commit.copy: source obun {pending.sourceObunId}, \
      case {caseId.toNat}, generated goal {newGoalId}"
    IO.mkRef $ Goal.mk {
      id := newGoalId
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
  let newKind := match pending.sourceObunKind with
    | .managed => .inherited pending.sourceObunId true
    | .duplicated => .inherited pending.sourceObunId false
    | _ => pending.sourceObunKind
  obunRef.modify λ o =>
    o.setKind newKind
      |>.setContextDepth pending.sourceObunDepth
      |>.setFullContextIrisSubgoals irisSubgoals
      |>.setGoals goalRefs

/- Make new rapp and goal according to the given RappSpec -/
def mkRappSpec (parentRef : GoalRef) (usedRule : Rule RuleInfo)
    (spec : RappSpec) : CoreM Q (RappRef × Array GoalRef) := do
  let obunRef ← mkInitialObunRef parentRef spec
  match spec.effect.action with
  | some (.splitGoals subgoals ..) =>
    applyMultipleGoalsEffect obunRef subgoals
  | some (.manageContext templates ..) =>
    applyContextManagementEffect obunRef templates
  | some (.closeGoal) =>
    applyCloseGoalEffect parentRef obunRef spec
  | none => pure ()
  let rappRef ← mkInitialRappRef parentRef obunRef usedRule spec.postState

  /- Record context-related info in the rapp node -/
  rappRef.modify λ r =>
    r.setUsedHyps spec.effect.usedHyps
    |>.setGeneratedSpatialHyps spec.effect.generatedSpatialHyps
  obunRef.modify λ o => o.setParent rappRef
  if (← obunRef.get).state.isProven then
    rappRef.modify λ r => r.setState .proven
  return (rappRef, (← obunRef.get).goals)

def commitRuleOutput (gref : GoalRef) (usedRule : Rule RuleInfo)
    (output : RuleOutput) : CoreM Q RuleResult := do
  if output.rappSepcs.isEmpty then return .failed
  let mut rappRefs := #[]
  let mut goalsToEnqueue := #[]
  for spec in output.rappSepcs do
    let (rappRef, goalRefs) ← mkRappSpec gref usedRule spec
    rappRefs := rappRefs.push rappRef
    goalsToEnqueue := goalsToEnqueue ++ goalRefs
  let provenBy? ← rappRefs.findM? fun rappRef => do
    return (← rappRef.get).state.isProven
  gref.modify fun goal =>
    let goal := goal.setChildren (goal.children ++ rappRefs)
    match provenBy? with
    | some _ => goal.setState .provenByRuleApplication
    | none => goal
  enqueueGoals goalsToEnqueue
  match provenBy? with
  | some _ => return .proved rappRefs
  | none => return .succeeded rappRefs

end Iris.ProofMode.Aesop.Search.Copy
