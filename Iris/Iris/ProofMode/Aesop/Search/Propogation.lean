module

public meta import Iris.ProofMode.Aesop.Search.SearchM
public meta import Iris.ProofMode.Aesop.Search.Types

public meta section

namespace Iris.ProofMode.Aesop.Search

open Lean Tactic Meta
open Iris.ProofMode

variable {Q : Type} [Queue Q]

-- Find the goal reference in this obligation bundle with the given goal ID.
private def findGoalById (oref : ObunRef) (id : GoalId) :
    SearchM Q (Option GoalRef) := do
  (← oref.get).goals.findM? λ gref => do
    return (← gref.get).id == id

private meta partial def collectUsedHyps (gref : GoalRef) : SearchM Q (Array IrisHyp) := do
  let g ← gref.get
  let here := g.state.usedIrisHyps?.getD #[]
  match g.origin with
  | .subgoal =>
    if g.mask.onlyOne then pure here
    else throwError "iaesop: internal error: collect used iris hypothesis's root is not the start one"
  | .copied fromId =>
    let some fromRef ← findGoalById g.parent fromId
      | throwError "iaesop: internal error: fromRef does not exist in current Obun"
    return (← collectUsedHyps fromRef) ++ here
  | .droppedMVar =>
    return here

private meta partial def collectUsedHypsByIndex
    (gref : GoalRef) : SearchM Q (Array (Nat × Array IrisHyp)) := do
  let g ← gref.get
  let here := g.state.usedIrisHyps?.getD #[]
  match g.origin with
  | .subgoal =>
    let some i := g.caseIndex?
      | throwError "iaesop: internal error: root split goal does not have case id"
    return #[(i, here)]
  | .copied fromId =>
    let some fromRef ← findGoalById g.parent fromId
      | throwError "iaesop: internal error: fromRef does not exist in current Obun"
    let prev ← collectUsedHypsByIndex fromRef
    let some i := g.caseIndex?
      | throwError "iaesop: internal error: copied goal does not have case id"
    return prev.push (i, here)
  | .droppedMVar =>
    return #[]

private partial def collectGoalLineageIds (gref : GoalRef) :
    SearchM Q (Array GoalId) := do
  let g ← gref.get
  match g.origin with
  | .copied fromId =>
    let some fromRef ← findGoalById g.parent fromId
      | throwError "iaesop: internal error: fromRef does not exist in current Obun"
    return (← collectGoalLineageIds fromRef).push g.id
  | .subgoal | .droppedMVar =>
    return #[g.id]

-- Store the used split context into the parent rule application.
private def writeUsedHypsToRapp
    (rappRef : RappRef) (usedByIndex : Array (Nat × Array IrisHyp)) :
    SearchM Q Unit := do
  let rapp ← rappRef.get
  let obun ← rapp.children.get
  let size := obun.fullContextIrisSubgoals.size
  let spatialSplits :=
    usedByIndex.foldl (init := #[]) λ ctx (i, irisHyps) =>
      (List.range size).foldl (init := #[]) λ acc j =>
        acc.push <| if i == j then irisHyps else ctx[j]?.getD #[]
  rappRef.modify λ r => r.setfinalizedSpatialSplits spatialSplits

-- Create copied metavariables for every uncovered split target.
private def mkCopiedGoalInfos
    (rapp : Rapp) (mask : ProgressMask)
    (state : Meta.SavedState) (sourceGoal : MVarId)
    (used : Array IrisHyp) :
    SearchM Q (Array CopiedGoalInfo × Meta.SavedState) := do
  let obun ← rapp.children.get
  let irisSubgoals := obun.fullContextIrisSubgoals
  -- Collect the remaing goal's index
  let remaining ← (List.range irisSubgoals.size).foldlM
      (init := (#[] : Array (Nat × IrisGoal))) λ acc i => do
    if mask.contains i then return acc
    match irisSubgoals[i]? with
    | some irisGoal => return acc.push (i, irisGoal)
    | none => throwError "iaesop: internal error: missing split target index"
  if remaining.isEmpty then
    return (#[], state)

  -- Generate new copied goals with propogated information
  liftM do
    state.restore
    let tag ← sourceGoal.getTag
    let infos ← remaining.foldlM (init := #[])
      λ (acc : Array CopiedGoalInfo) (i, irisGoal) => do
        let irisGoal ← used.foldlM (init := irisGoal)
          λ (irisGoal : IrisGoal) (usedHyp : IrisHyp) => do
            if !irisGoal.hyps.spatialIVarIds.contains usedHyp.ivar then
              throwError
                "iaesop: internal error: used Iris hypothesis is absent from copied goal context"
            let ⟨e', hyps', _, _, _, _, _⟩ :=
              irisGoal.hyps.remove false usedHyp.ivar
            return { irisGoal with e := e', hyps := hyps' }
        let goalExpr ← mkFreshExprSyntheticOpaqueMVar (IrisGoal.toExpr irisGoal) tag
        let goal := goalExpr.mvarId!
        let goalType ← ppExpr (← goal.getType)
        dbg_trace s!"iaesop.copy: generated copied goal at index {i}: {goalType.pretty}"
        return acc.push { index := i, goal, mvars := (← goal.getMVarDependencies) }
    return (infos, ← saveState)

-- Insert copied metavariables as active goals in the current obun.
private def appendCopiedGoalInfos
    (g : Goal) (obunRef : ObunRef) (postState : Meta.SavedState)
    (infos : Array CopiedGoalInfo) : SearchM Q Unit := do
  let currentIteration ← getIteration
  let newGoalRefs ← infos.mapM λ info => do
    dbg_trace s!"iaesop.copy: enqueue copied goal from {g.id}, index {info.index}, mask {repr (g.mask.mark info.index)}"
    IO.mkRef $ Goal.mk {
      id := ← getAndIncrementNextGoalId
      mask := g.mask.mark info.index
      caseId := CaseId.ofIndex info.index
      parent := obunRef
      children := #[]
      origin := .copied g.id
      depth := g.depth + 1
      state := .unknown
      isIrrelevant := false
      isForcedUnprovable := false
      preNormGoal := info.goal
      preNormState := postState
      normalizationState := .notNormal
      unassignedMvars := info.mvars
      successProbability := g.successProbability
      addedInIteration := currentIteration
      lastExpandedInIteration := .zero
      rulesQueue := {}
      appendiedGoalId := #[]
    }
  obunRef.modify λ o => o.setGoals (o.goals ++ newGoalRefs)
  enqueueGoals newGoalRefs

private def Goal.currentSavedState (g : Goal) : Meta.SavedState :=
  match g.normalizationState with
  | .notNormal => g.preNormState
  | .normal _ postState _ => postState
  | .provenByNorm postState _ => postState

private def appendCopiedGoalsFromProvenGoal (gref : GoalRef) : SearchM Q Unit := do
  let g ← gref.get
  let used ← collectUsedHyps gref
  let obunRef := g.parent
  let obun ← obunRef.get
  let some rappRef := obun.parent?
    | return
  let rapp ← rappRef.get

  let state := Goal.currentSavedState g
  let sourceGoal := g.normalizationState.normalizedGoal?.getD g.preNormGoal
  let (infos, postState) ←
    mkCopiedGoalInfos rapp g.mask state sourceGoal used
  if infos.isEmpty then
    return
  appendCopiedGoalInfos g obunRef postState infos

private def allGoalsProven (goals : Array GoalRef) : SearchM Q Bool := do
  goals.allM λ gref => return (← gref.get).state.isProven

mutual

meta partial def markGoalIrrelevant (gref : GoalRef) : SearchM Q Unit := do
  let g ← gref.get
  if g.isIrrelevant then
    return
  gref.modify λ g => g.setIsIrrelevant true
  for rref in g.children do
    markRappIrrelevant rref

meta partial def markRappIrrelevant (rref : RappRef) : SearchM Q Unit := do
  let r ← rref.get
  if r.isIrrelevant then
    return
  rref.modify λ r => r.setIsIrrelevant true
  markObunIrrelevant r.children

meta partial def markObunIrrelevant (oref : ObunRef) : SearchM Q Unit := do
  let o ← oref.get
  if o.isIrrelevant then
    return
  oref.modify λ o => o.setIsIrrelevant true
  for gref in o.goals do
    markGoalIrrelevant gref

end

private def markOtherObunsIrrelevant
    (_rappRef : RappRef) (_keepObunRef : ObunRef) : SearchM Q Unit :=
  return ()

private def markOtherRappsIrrelevant
    (goalRef : GoalRef) (keepRappRef : RappRef) : SearchM Q Unit := do
  let keepId := (← keepRappRef.get).id
  for rref in (← goalRef.get).children do
    if (← rref.get).id != keepId then
      markRappIrrelevant rref

private def markOtherGoalsIrrelevant
    (obunRef : ObunRef) (keepIds : Array GoalId) : SearchM Q Unit := do
  for gref in (← obunRef.get).goals do
    if !keepIds.contains (← gref.get).id then
      markGoalIrrelevant gref

mutual

meta partial def propogateFromGoal (gref : GoalRef) : SearchM Q Unit := do
  let g ← gref.get
  if !g.state.isProven then
    throwError "iaesop: internal error : unproved goal should not be propagated"

  let obunRef := g.parent
  let obun ← obunRef.get
  if obun.state.isProven then
    return
  -- Plain obuns do not own a context split, so they only close after all
  -- their children have been proven.
  if obun.kind.isPlain then
    if ← allGoalsProven obun.goals then
      obunRef.modify λ o => o.setState .proven
      propogateFromObun obunRef
    return

  -- If still goal left, generate new goals for expansion.
  if !g.mask.isComplete then
    appendCopiedGoalsFromProvenGoal gref
    return

  -- Otherwise, record the completed context split info and propagate upward.
  let usedByIndex ← collectUsedHypsByIndex gref
  let keepIds ← collectGoalLineageIds gref
  obunRef.modify λ o => o.setState .proven
  markOtherGoalsIrrelevant obunRef keepIds
  let some rappRef := obun.parent?
    | return
  writeUsedHypsToRapp rappRef usedByIndex
  propogateFromObun obunRef

meta partial def propogateFromObun (obunRef : ObunRef) : SearchM Q Unit := do
  let obun ← obunRef.get
  if !obun.state.isProven then
    throwError "iaesop: internal error : unproved obun should not be propogated"

  let some rappRef := obun.parent?
    | return
  let rapp ← rappRef.get
  if rapp.state.isProven then
    throwError "iaesop: internal error: rapp already be proven, can not be marked again"
  markOtherObunsIrrelevant rappRef obunRef
  rappRef.modify λ r => r.setState .proven
  propogateFromRapp rappRef

meta partial def propogateFromRapp (rappRef : RappRef) : SearchM Q Unit := do
  let rapp ← rappRef.get
  if !rapp.state.isProven then
    throwError "iaesop: internal error: unproved rapp should not be propagated"

  let used :=
    rapp.finalizedSpatialSplits.foldl
      (init := rapp.consumedSpatialHyp?.toArray) λ acc hyps => acc ++ hyps
  let parentRef := rapp.parent
  markOtherRappsIrrelevant parentRef rappRef
  parentRef.modify λ g => g.setState (.provenByRuleApplication used)
  propogateFromGoal parentRef

end
end Search
