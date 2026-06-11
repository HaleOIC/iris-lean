module

public meta import Iris.ProofMode.Aesop.Rule.Dispatch
public meta import Iris.ProofMode.Aesop.Search.Normalization
public meta import Iris.ProofMode.Aesop.Search.Tracing
public meta import Iris.ProofMode.Tactics.Cases
public meta import Iris.ProofMode.Tactics.Exact
public meta import Iris.ProofMode.Tactics.Exists
public meta import Iris.ProofMode.Tactics.Have

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

private def appliedHypTacticIdent? : AppliedHyp → Option (TSyntax `ident)
  | .spatial hyp | .intuitionistic hyp => some (mkIdent hyp.name)
  | .lean userName _ => some (mkIdent userName)

private def irisHypFrameIdent (hyp : IrisHyp) : TSyntax `frameIdent :=
  ⟨mkIdent hyp.name⟩

private def mkSpatialSpecPat (hyps : Array IrisHyp) : MetaM (TSyntax `specPat) := do
  let names := hyps.map irisHypFrameIdent
  `(specPat| [$[$names:frameIdent]*])

private def mkIApplyTactic (fn : TSyntax `term) (obun : Obun) :
    MetaM (TSyntax `tactic) := do
  if obun.finalizedSpatialSplits.isEmpty then
    `(tactic| iapply $fn:term)
  else
    let spats ← obun.finalizedSpatialSplits.mapM mkSpatialSpecPat
    `(tactic| iapply $fn:term $$ $spats:specPat*)

/-- Reconstruct the surface tactic that a replayed rule corresponds to. Rules
without a faithful surface representation fall back to `skip` so that the
rendered tactic chain stays structurally consistent. -/
private def mkReplayTactic (rapp : Rapp) (obun : Obun) (config : SearchConfig) :
    MetaM (TSyntax `tactic) := do
  let fallback ← `(tactic| skip)
  match rapp.appliedRule.info.builder with
  | .backward =>
      let decl := mkIdent rapp.appliedRule.id.name
      mkIApplyTactic decl obun
  | .tactic .ipureIntro =>
      let solver : TSyntax `tactic := ⟨config.pureSolver⟩
      `(tactic| (ipureintro; $solver:tactic))
  | .tactic .iexist => `(tactic| iexists _)
  | .tactic .icases =>
      match rapp.usedHyp? >>= appliedHypTacticIdent? with
      | some ident =>
          let binder ← `(binderIdent| $ident:ident)
          let pat ← `(icasesPat| ($binder:binderIdent | $binder:binderIdent))
          `(tactic| icases $ident:term with $pat:icasesPat)
      | none => pure fallback
  | .tactic .isplit => `(tactic| isplit)
  | .tactic .ileft => `(tactic| ileft)
  | .tactic .iright => `(tactic| iright)
  | .tactic .imodIntro => `(tactic| imodintro)
  | .tactic .imod =>
      match rapp.usedHyp? >>= appliedHypTacticIdent? with
      | some ident =>
          /- Name the modal-elimination result so later steps that reference the
          generated hypothesis resolve to the same name. -/
          match rapp.generatedSpatialHyps[0]? with
          | some gen =>
              let genName := mkIdent gen.name
              let genBi ← `(binderIdent| $genName:ident)
              let genPat ← `(icasesPat| $genBi:binderIdent)
              `(tactic| imod $ident:term with $genPat:icasesPat)
          | none => `(tactic| imod $ident:term)
      | none => pure fallback
  | .tactic .identity =>
      /- The identity rule performs a spatial split `P ∗ Q`; the left context
      goes to the first subgoal via `isplitl [..]`. -/
      match obun.finalizedSpatialSplits[0]? with
      | some leftCtx =>
          let leftIdents := leftCtx.map (fun h => mkIdent h.name)
          `(tactic| isplitl [$leftIdents*])
      | none => pure fallback
  | .tactic .applyHyps =>
      match rapp.usedHyp? >>= appliedHypTacticIdent? with
      | some ident =>
          /- A `close` application (no remaining child goals) discharges the
          goal directly, so emit `iexact`; otherwise the hypothesis is applied. -/
          if obun.goals.isEmpty || obun.kind.isInherited then
            `(tactic| iexact $ident:ident)
          else
            mkIApplyTactic ident obun
      | none => pure fallback
  | .tactic .haveHyps =>
      match rapp.usedHyp? >>= appliedHypTacticIdent?, rapp.generatedSpatialHyps[0]? with
      | some usedIdent, some generatedHyp =>
          let generatedIdent := mkIdent generatedHyp.name
          let generatedBinder ← `(binderIdent| $generatedIdent:ident)
          let generatedPat ← `(icasesPat| $generatedBinder:binderIdent)
          let premiseContexts :=
            obun.finalizedSpatialSplits.extract 0 (obun.goals.size - 1)
          if premiseContexts.isEmpty then
            pure fallback
          else
            let spats ← premiseContexts.mapM mkSpatialSpecPat
            `(tactic| ihave $generatedPat:icasesPat := $usedIdent:term $$ $spats:specPat*)
      | _, _ => pure fallback
  | _ => pure fallback

private def recordScriptStep (rref : RappRef) (obun : Obun) (preState : SavedState)
    (preGoal : MVarId) (postGoals : Array MVarId) : ReplayM Unit := do
  if !(← readThe ReplayM.Context).config.generateScript? then
    return
  let config := (← readThe ReplayM.Context).config
  let rapp ← rref.get
  let tactic ← liftM <| mkReplayTactic rapp obun config
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
  | throwError "iaesop(baseline): replay procedure could not find a proven rapp to move"

  /- Call the proven rules' corresponding replay function -/
  let rapp ← rref.get
  let obun ← rapp.children.get
  liftM <| Search.traceReplayStep goalMVarId (toString rapp.appliedRule.info.builder)
  let preState ← liftM (show MetaM SavedState from saveState)
  let goalMVarIds ← liftM <|
    rapp.appliedRule.info.builder.replay { goal := goalMVarId, rapp, config }
  recordScriptStep rref obun preState goalMVarId goalMVarIds

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
    assignProof goalRef
    return ()

  /- Find the proven child goal that replay should follow next. -/
  let sourceObunId := match obun.kind with
    | .inherited sourceId _ => sourceId
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
    assignProof nextGoalRef
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
  assignProof nextGoalRef

/- (Baseline) Replay proof entry point -/
public meta def replayProof : SearchM Q Unit := do
  let config := (← readThe SearchM.Context).config
  let rootRef ← getRootGoal
  let rootGoal ← rootRef.get
  if !rootGoal.state.isProven then
    throwError "iaesop(baseline): replay procedure reach an unproven goal"

  /- Make sure goal's mvarId has not been assigned -/
  let rootMVarId := rootGoal.normalizationState.normalizedGoal?.getD rootGoal.preNormGoal
  let assigned ← liftM (m := MetaM) rootMVarId.isAssignedOrDelayedAssigned
  if assigned then return

  /- Enter the replay context -/
  rootGoal.preNormState.restore
  let (_, replayState) ← liftM (m := ProofModeM) <|
    ReaderT.run (assignProof rootRef) { config } |>.run {
      focus := rootGoal.preNormGoal
      pendingByCase := {}
    }
  if !replayState.pendingByCase.isEmpty then
    throwError "iaesop(baseline): replay finished with pending split cases"
