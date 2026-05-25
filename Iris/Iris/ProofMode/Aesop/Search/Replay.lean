module

public meta import Iris.ProofMode.Aesop.Rule.Common.Main
public meta import Iris.ProofMode.Aesop.Search.Normalization

public meta section

namespace Iris.ProofMode.Aesop.Baseline

open Lean Meta Qq Std

variable {Q : Type} [Queue Q]

/- Replay's related Monad -/
private structure ReplayM.Context where
  config : SearchConfig

private structure ReplayM.State where
  /- Current metavariable followed by the replay procedure. -/
  focus : MVarId
  /- Generated replay metavariables, keyed by source context split and case. -/
  pendingByCase : Std.HashMap (ObunId × CaseId) MVarId
  deriving Inhabited

private abbrev ReplayM :=
  ReaderT ReplayM.Context $ StateRefT ReplayM.State ProofModeM

/- Assign the proof term following the proven chain -/
/- [Note] We should follow the tree but with different goal (real replay stage) MVarId -/
private partial def assignProof (goal : Goal) : ReplayM Unit := do
  /- First check the normalization stage's change -/
  let goalMVarId := (← getThe ReplayM.State).focus
  let config := (← readThe ReplayM.Context).config
  let result ← liftM do
    normalizeGoalMVar goalMVarId goal.depth config.maxNormIterations
      config.enableSimp? goal.unassignedMvars
  let some goalMVarId := match result with
    | .proved => none
    | .changed goalMVarId => some goalMVarId
    | .unchanged => some goalMVarId
  | return () -- Already proved, nothing to do

  /- Find an already proven Rapp node to replay -/
  let some rref ← goal.children.findM? λ rref => do
    let rapp ← rref.get
    return rapp.state.isProven && !rapp.isIrrelevant
  | throwError "iaesop(baseline): replay procedure could not find a proven rapp to move"

  /- Call the proven rules' corresponding replay function -/
  let rapp ← rref.get
  let obun ← rapp.children.get
  let goalMVarIds ← liftM <| RuleRunnerDescr.ofInfo rapp.appliedRule.info |>.replay
    { goal := goalMVarId, rapp }

  /- The replayed rule closed the focused metavariable and produced no children. -/
  if goalMVarIds.isEmpty && obun.goals.isEmpty then
    if !(← getThe ReplayM.State).pendingByCase.isEmpty then
      throwError "iaesop(baseline): replay closed the focus while split cases are still pending"
    return ()

  /- Select the focus goal and record the remaining -/
  if goalMVarIds.size == 1 then
    let some goalMVarId := goalMVarIds[0]?
      | throwError "iaesop(baseline): replay returned an inconsistent singleton goal array"
    let state ← getThe ReplayM.State
    set { state with focus := goalMVarId }

    if obun.goals.size != 1 then
      throwError s!"iaesop(baseline): replay produced one goal but search child obun has {obun.goals.size} goals"
    let some goalRef := obun.goals[0]?
      | throwError "iaesop(baseline): child obun has no goal at index 0"
    assignProof (← goalRef.get)
    return ()

  /- Find the proven child goal that replay should follow next. -/
  let sourceObunId := match obun.kind with
    | .inherited sourceId => sourceId
    | _ => obun.id
  let some nextGoalRef ← obun.goals.findM? λ gref => do
    let goal ← gref.get
    return goal.state.isProven && !goal.isIrrelevant
  | throwError "iaesop(baseline): replay could not find a proven child goal to resume"
  let nextGoal ← nextGoalRef.get
  let some nextCaseId := nextGoal.caseId?
    | throwError "iaesop(baseline): replay cannot resume from a child goal without case id"
  let nextKey := (sourceObunId, nextCaseId)

  /- If this rule closed the current metavariable, resume from a pending split case. -/
  if goalMVarIds.isEmpty then
    let state ← getThe ReplayM.State
    let some goalMVarId := state.pendingByCase.get? nextKey
      | throwError "iaesop(baseline): replay has no pending metavariable for the next split case"
    set {
      state with
      focus := goalMVarId
      pendingByCase := state.pendingByCase.erase nextKey
    }
    assignProof nextGoal
    return ()

  if goalMVarIds.size != obun.goals.size then
    throwError s!"iaesop(baseline): replay produced {goalMVarIds.size} goals but search child obun has {obun.goals.size} goals"

  /- Collect generated metavariables by split case, then update replay state once. -/
  let state ← getThe ReplayM.State
  let (_, pendingByCase) ← obun.goals.foldlM (init := (0, state.pendingByCase))
      λ (idx, pendingByCase) goalRef => do
    let some goalMVarId := goalMVarIds[idx]?
      | throwError "iaesop(baseline): replay result array is missing a generated goal"
    let some caseId := (← goalRef.get).caseId?
      | throwError "iaesop(baseline): replay generated split goals for a child without case id"
    return (idx + 1, pendingByCase.insert (sourceObunId, caseId) goalMVarId)
  let some goalMVarId := pendingByCase.get? nextKey
    | throwError "iaesop(baseline): replay has no generated metavariable for the proven child case"
  set {
    state with
    focus := goalMVarId
    pendingByCase := pendingByCase.erase nextKey
  }
  assignProof nextGoal

/- (Baseline) Replay proof entry point -/
public meta def replayProof : SearchM Q Unit := do
  let config := (← readThe SearchM.Context).config
  let rootGoal ← (← getRootGoal).get
  if !rootGoal.state.isProven then
    throwError "iaesop(baseline): replay procedure reach an unproven goal"

  /- Make sure goal's mvarId has not been assigned -/
  let rootMVarId := rootGoal.normalizationState.normalizedGoal?.getD rootGoal.preNormGoal
  let assigned ← liftM (m := MetaM) rootMVarId.isAssignedOrDelayedAssigned
  if assigned then return

  /- Enter the replay context -/
  rootGoal.preNormState.restore
  let (_, replayState) ← liftM (m := ProofModeM) <|
    ReaderT.run (assignProof rootGoal) { config } |>.run {
      focus := rootGoal.preNormGoal
      pendingByCase := {}
    }
  if !replayState.pendingByCase.isEmpty then
    throwError "iaesop(baseline): replay finished with pending split cases"
