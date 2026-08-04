module

public meta import Iris.ProofMode.Aesop.Rule.Dispatch
public meta import Iris.ProofMode.Aesop.Search.Shared.Normalization
public meta import Iris.ProofMode.Aesop.Search.Shared.Replay
public meta import Iris.ProofMode.Aesop.Search.Shared.Tracing
public meta import Iris.ProofMode.Tactics.Cases
public meta import Iris.ProofMode.Tactics.Exact
public meta import Iris.ProofMode.Tactics.Exists
public meta import Iris.ProofMode.Tactics.Have

public meta section

namespace Iris.ProofMode.Aesop.Search.Copy

open Iris.ProofMode.Aesop

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
  /- Pure Lean goals deliberately exposed by `pureStop`. -/
  remainingGoals : Array MVarId
  deriving Inhabited

private abbrev ReplayM :=
  ReaderT ReplayM.Context $ StateRefT ReplayM.State ProofModeM

private def recordScriptStep (rref : RappRef) (obun : Obun) (preState : SavedState)
    (preGoal : MVarId) (postGoals : Array MVarId) : ReplayM Unit := do
  if !(← readThe ReplayM.Context).config.generateScript? then
    return
  let config := (← readThe ReplayM.Context).config
  let rapp ← rref.get
  let tactic ← liftM <| Shared.mkReplayTactic rapp obun config
  let postState ← liftM (show MetaM SavedState from saveState)
  rref.modify λ rapp =>
    rapp.setScriptSteps? <| some #[
      { preState, preGoal, tactic, postState, postGoals }
    ]

/- Store the reconstructed normalization tactics on the goal so that script
generation can prepend them ahead of the rule applications. -/
private def setNormScript (gref : GoalRef) (steps : Array Script.LazyStep) :
    ReplayM Unit := do
  if !(← readThe ReplayM.Context).config.generateScript? || steps.isEmpty then
    return
  let entry : Array (DisplayRuleId × Option (Array Script.LazyStep)) :=
    #[(.normSimp, some steps)]
  gref.modify fun g =>
    let ns := match g.normalizationState with
      | .notNormal => .notNormal
      | .normal pg ps gen used _ => .normal pg ps gen used entry
      | .provenByNorm ps gen used _ => .provenByNorm ps gen used entry
    g.setNormalizationState ns

/- Assign the proof term following the proven chain -/
/- [Note] We should follow the tree but with different goal (real replay stage) MVarId -/
private partial def assignProof (gref : GoalRef) : ReplayM Unit := do
  let goal ← gref.get
  /- First check the normalization stage's change -/
  let goalMVarId := (← getThe ReplayM.State).focus
  let config := (← readThe ReplayM.Context).config
  let (result, normScript) ← liftM do
    normalizeGoalMVar goalMVarId goal.depth config.maxNormIterations
      config.enableSimp? goal.unassignedMvars (recordScript := config.generateScript?)
  setNormScript gref normScript
  let some goalMVarId := match result with
    | .proved => none
    | .changed goalMVarId => some goalMVarId
    | .unchanged => some goalMVarId
  | return () -- Already proved, nothing to do

  /- Find an already proven Rapp node to replay -/
  let some rref ← goal.children.findM? λ rref => do
    let rapp ← rref.get
    return rapp.state.isProven && !rapp.isIrrelevant
  | throwError "iaesop(copy): replay procedure could not find a proven rapp to move"

  /- Call the proven rules' corresponding replay function -/
  let rapp ← rref.get
  let obun ← rapp.children.get
  liftM <| Search.traceReplayStep goalMVarId (toString rapp.appliedRule.info.builder)
  let preState ← liftM (show MetaM SavedState from saveState)
  let replayGoalMVarIds ← liftM <|
    rapp.appliedRule.info.builder.replay { goal := goalMVarId, rapp, config }
  recordScriptStep rref obun preState goalMVarId replayGoalMVarIds

  /- `pureStop` deliberately leaves the Lean goal returned by `ipureintro`
  open. Record it for the caller, but treat this search branch as closed while
  replay continues through any pending Iris siblings. -/
  let isPureStop :=
    config.pureStop? && rapp.appliedRule.info.builder == .tactic .ipureIntro
  let goalMVarIds ←
    if isPureStop then
      modifyThe ReplayM.State λ state =>
        { state with remainingGoals := state.remainingGoals ++ replayGoalMVarIds }
      pure #[]
    else
      pure replayGoalMVarIds

  /- The replayed rule closed the focused metavariable and produced no children. -/
  if goalMVarIds.isEmpty && obun.goals.isEmpty then
    if !(← getThe ReplayM.State).pendingByCase.isEmpty then
      throwError "iaesop(copy): replay closed the focus while split cases are still pending"
    return ()

  /- Select the focus goal and record the remaining -/
  if goalMVarIds.size == 1 then
    let some goalMVarId := goalMVarIds[0]?
      | throwError "iaesop(copy): replay returned an inconsistent singleton goal array"
    let state ← getThe ReplayM.State
    set { state with focus := goalMVarId }

    if obun.goals.size != 1 then
      throwError s!"iaesop(copy): replay produced one goal but search child obun has {obun.goals.size} goals"
    let some goalRef := obun.goals[0]?
      | throwError "iaesop(copy): child obun has no goal at index 0"
    assignProof goalRef
    return ()

  /- Find the proven child goal that replay should follow next. -/
  let sourceObunId := match obun.kind with
    | .inherited sourceId _ => sourceId
    | _ => obun.id
  let some nextGoalRef ← obun.goals.findM? λ gref => do
    let goal ← gref.get
    return goal.state.isProven && !goal.isIrrelevant
  | throwError "iaesop(copy): replay could not find a proven child goal to resume"
  let nextGoal ← nextGoalRef.get
  let some nextCaseId := nextGoal.caseId?
    | throwError "iaesop(copy): replay cannot resume from a child goal without case id"
  let nextKey := (sourceObunId, nextCaseId)

  /- If this rule closed the current metavariable, resume from a pending split case. -/
  if goalMVarIds.isEmpty then
    let state ← getThe ReplayM.State
    let some goalMVarId := state.pendingByCase.get? nextKey
      | throwError "iaesop(copy): replay has no pending metavariable for the next split case"
    set {
      state with
      focus := goalMVarId
      pendingByCase := state.pendingByCase.erase nextKey
    }
    assignProof nextGoalRef
    return ()

  if goalMVarIds.size != obun.goals.size then
    throwError s!"iaesop(copy): replay produced {goalMVarIds.size} goals but search child obun has {obun.goals.size} goals"

  /- Collect generated metavariables by split case, then update replay state once. -/
  let state ← getThe ReplayM.State
  let (_, pendingByCase) ← obun.goals.foldlM (init := (0, state.pendingByCase))
      λ (idx, pendingByCase) goalRef => do
    let some goalMVarId := goalMVarIds[idx]?
      | throwError "iaesop(copy): replay result array is missing a generated goal"
    let some caseId := (← goalRef.get).caseId?
      | throwError "iaesop(copy): replay generated split goals for a child without case id"
    return (idx + 1, pendingByCase.insert (sourceObunId, caseId) goalMVarId)
  let some goalMVarId := pendingByCase.get? nextKey
    | throwError "iaesop(copy): replay has no generated metavariable for the proven child case"
  set {
    state with
    focus := goalMVarId
    pendingByCase := pendingByCase.erase nextKey
  }
  assignProof nextGoalRef

/- (Baseline) Replay proof entry point -/
public meta def replayProof : CoreM Q (Array MVarId) := do
  let config := (← readThe CoreM.Context).config
  let rootRef ← getRootGoal
  let rootGoal ← rootRef.get
  if !rootGoal.state.isProven then
    throwError "iaesop(copy): replay procedure reach an unproven goal"

  /- Make sure goal's mvarId has not been assigned -/
  let rootMVarId := rootGoal.normalizationState.normalizedGoal?.getD rootGoal.preNormGoal
  let assigned ← liftM (m := MetaM) rootMVarId.isAssignedOrDelayedAssigned
  /- A root-level `pureStop` application may have assigned the speculative
  search goal directly. Restore and replay it so we can return the newly
  exposed pure Lean metavariable to the tactic frontend. -/
  if assigned && !config.pureStop? then return #[]

  /- Enter the replay context -/
  rootGoal.preNormState.restore
  let (_, replayState) ← liftM (m := ProofModeM) <|
    ReaderT.run (assignProof rootRef) { config } |>.run {
      focus := rootGoal.preNormGoal
      pendingByCase := {}
      remainingGoals := #[]
    }
  if !replayState.pendingByCase.isEmpty then
    throwError "iaesop(copy): replay finished with pending split cases"
  return replayState.remainingGoals
