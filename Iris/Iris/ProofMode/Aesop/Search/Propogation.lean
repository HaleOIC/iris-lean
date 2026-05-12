module

public meta import Iris.ProofMode.Aesop.Search.SearchM
public meta import Iris.ProofMode.Aesop.Search.Expansion
public meta import Iris.ProofMode.Tactics.Assumption
public meta import Iris.ProofMode.Tactics.Split

public meta section

namespace Iris.ProofMode.Aesop.Search

open Lean Tactic Meta
open Iris.ProofMode

variable {Q : Type} [Queue Q]

private def findGoalById (oref : ObunRef) (id : GoalId) :
    SearchM Q (Option GoalRef) := do
  for gref in (← oref.get).goals do
    if (← gref.get).id == id then
      return some gref
  return none

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
    let some i := g.mask.onlyOneIndex?
      | throwError "iaesop: internal error: root split goal does not have singleton mask"
    return #[(i, here)]
  | .copied fromId =>
    let some fromRef ← findGoalById g.parent fromId
      | throwError "iaesop: internal error: fromRef does not exist in current Obun"
    let prev ← collectUsedHypsByIndex fromRef
    let prevMask := (← fromRef.get).mask
    let some i := g.mask.firstNewBit? prevMask
      | throwError "iaesop: internal error: copied goal did not add exactly one mask bit"
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

private structure CopiedGoalInfo where
  index : Nat
  goal : MVarId
  mvars : Std.HashSet MVarId
  deriving Inhabited

-- Replace the Iris context entry at an index while preserving the array size.
private def setIrisContextAt
    (size : Nat) (ctx : Array (Array IrisHyp))
    (i : Nat) (hyps : Array IrisHyp) : Array (Array IrisHyp) :=
  (List.range size).foldl (init := #[]) λ acc j =>
    let old := ctx[j]?.getD #[]
    acc.push <| if j == i then hyps else old

-- Store the used split context into the parent rule application.
private def writeUsedHypsToRapp
    (rappRef : RappRef) (usedByIndex : Array (Nat × Array IrisHyp)) :
    SearchM Q Unit := do
  let rapp ← rappRef.get
  let size := rapp.irisSubgoals.size
  let irisContext :=
    usedByIndex.foldl (init := rapp.irisContext) λ ctx (i, irisHyps) =>
      setIrisContextAt size ctx i irisHyps
  dbg_trace s!"iaesop.copy: finalized context split with used hyps by index: {usedByIndex.map (λ x => (x.1, x.2.size))}"
  rappRef.modify λ r => r.setIrisContext irisContext

-- Create copied metavariables for every uncovered split target.
private def mkCopiedGoalInfos
    (rapp : Rapp) (mask : ProgressMask)
    (state : Meta.SavedState) (sourceGoal : MVarId)
    (used : Array IrisHyp) :
    SearchM Q (Array CopiedGoalInfo × Meta.SavedState) := do
  -- Collect the remaing goal's index
  let remaining ← (List.range rapp.irisSubgoals.size).foldlM
      (init := (#[] : Array (Nat × IrisGoal))) λ acc i => do
    if mask.contains i then return acc
    match rapp.irisSubgoals[i]? with
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
    }
  obunRef.modify λ o =>
    o.setGoals (o.goals ++ newGoalRefs)
      |>.setMetaState? (some postState)
  enqueueGoals newGoalRefs

private def appendCopiedGoalsFromProvenGoal (gref : GoalRef) : SearchM Q Unit := do
  let g ← gref.get
  let used ← collectUsedHyps gref
  let obunRef := g.parent
  let obun ← obunRef.get
  let some rappRef := obun.parent?
    | return
  let rapp ← rappRef.get

  let state := obun.metaState?.getD g.preNormState
  let sourceGoal := g.normalizationState.normalizedGoal?.getD g.preNormGoal
  let (infos, postState) ←
    mkCopiedGoalInfos rapp g.mask state sourceGoal used
  if infos.isEmpty then
    return
  appendCopiedGoalInfos g obunRef postState infos

private def allGoalsProven (goals : Array GoalRef) : SearchM Q Bool := do
  for gref in goals do
    if !(← gref.get).state.isProven then
      return false
  return true

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
  for oref in r.children do
    markObunIrrelevant oref

meta partial def markObunIrrelevant (oref : ObunRef) : SearchM Q Unit := do
  let o ← oref.get
  if o.isIrrelevant then
    return
  oref.modify λ o => o.setIsIrrelevant true
  for gref in o.goals do
    markGoalIrrelevant gref

end

private def markOtherObunsIrrelevant
    (rappRef : RappRef) (keepObunRef : ObunRef) : SearchM Q Unit := do
  let keepId := (← keepObunRef.get).id
  let rapp ← rappRef.get
  dbg_trace s!"iaesop.prune: keep obun {keepId} under rapp {rapp.id}"
  for oref in rapp.children do
    if (← oref.get).id != keepId then
      markObunIrrelevant oref

private def markOtherRappsIrrelevant
    (goalRef : GoalRef) (keepRappRef : RappRef) : SearchM Q Unit := do
  let keepId := (← keepRappRef.get).id
  let goal ← goalRef.get
  dbg_trace s!"iaesop.prune: keep rapp {keepId} under goal {goal.id}"
  for rref in goal.children do
    if (← rref.get).id != keepId then
      markRappIrrelevant rref

private def markOtherGoalsIrrelevant
    (obunRef : ObunRef) (keepIds : Array GoalId) : SearchM Q Unit := do
  let obun ← obunRef.get
  dbg_trace s!"iaesop.prune: keep goal lineage {keepIds.map (·.toNat)} under obun {obun.id}"
  for gref in obun.goals do
    if !keepIds.contains (← gref.get).id then
      markGoalIrrelevant gref

mutual

meta partial def propogateProvenFromGoal (gref : GoalRef) : SearchM Q Unit := do
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
      propogateProvenFromObun obunRef
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
  propogateProvenFromObun obunRef

meta partial def propogateProvenFromObun (obunRef : ObunRef) : SearchM Q Unit := do
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
  propogateProvenFromRapp rappRef

meta partial def propogateProvenFromRapp (rappRef : RappRef) : SearchM Q Unit := do
  let rapp ← rappRef.get
  if !rapp.state.isProven then
    throwError "iaesop: internal error: unproved rapp should not be propagated"

  let used := rapp.irisContext.foldl (init := #[]) λ acc hyps => acc ++ hyps
  let parentRef := rapp.parent
  markOtherRappsIrrelevant parentRef rappRef
  parentRef.modify λ g => g.setState (.provenByRuleApplication used)
  propogateProvenFromGoal parentRef

end

end Search
