module

public meta import Iris.ProofMode.Aesop.Rule.Dispatch
public meta import Iris.ProofMode.Aesop.Search.Shared.Normalization
public meta import Iris.ProofMode.Aesop.Search.Shared.Replay
public meta import Iris.ProofMode.Aesop.Search.Bubble.Propagation

public meta section

namespace Iris.ProofMode.Aesop.Search.Bubble

open Lean Meta
open Iris.ProofMode
open Iris.ProofMode.Aesop

variable {Q : Type} [Queue Q]

private def getConfig : BubbleM Q SearchConfig :=
  liftM (m := Iris.ProofMode.Aesop.CoreM Q) do
    return (← readThe Iris.ProofMode.Aesop.CoreM.Context).config

private def recordRuleScript (rappRef : RappRef) (obun : Obun)
    (preState : SavedState) (preGoal : MVarId) (postGoals : Array MVarId)
    (config : SearchConfig) : BubbleM Q Unit := do
  if !config.generateScript? then return
  let rapp ← rappRef.get
  let tactic ← liftM (m := ProofModeM) <|
    Shared.mkReplayTactic rapp obun config
  let postState ← liftM (m := ProofModeM) <|
    liftM (m := MetaM) saveState
  appendProofScript #[{ preState, preGoal, tactic, postState, postGoals }]

private def emitScriptSuggestion : BubbleM Q Unit := do
  let script ← getProofScript
  let rootRef ← liftM (m := Iris.ProofMode.Aesop.CoreM Q) getRootGoal
  let root ← rootRef.get
  liftM (m := Iris.ProofMode.Aesop.CoreM Q) <| liftM (m := ProofModeM) do
    let tactics ← script.render root.preNormGoal
    Script.addTryThisTacticSeqSuggestion (← getRef) tactics

private def selectedSplits (children : Array BubbleId) :
    BubbleM Q (Array (Array IrisHyp)) :=
  children.mapM fun id => return (← getBubble id).consumed

private def findReplayableChild (pending : Array (BubbleId × MVarId))
    (completed : Array BubbleId) : BubbleM Q (Option Nat) := do
  let rec go (index : Nat) : BubbleM Q (Option Nat) := do
    if h : index < pending.size then
      let bubble ← getBubble pending[index].1
      if bubble.pre.all completed.contains then return some index
      go (index + 1)
    else
      return none
  go 0

mutual

private partial def assignSelectedChildren
    (pending : Array (BubbleId × MVarId)) (completed : Array BubbleId)
    (remaining : Array MVarId) : BubbleM Q (Array MVarId) := do
  if pending.isEmpty then return remaining
  let some index ← findReplayableChild pending completed
    | throwError "iaesop(bubble): selected bubbles contain an unsatisfied pre-index cycle"
  let some (bubbleId, goal) := pending[index]?
    | throwError "iaesop(bubble): replayable child index is out of bounds"
  let childRemaining ← assignBubble bubbleId goal
  let pending := pending.extract 0 index ++ pending.extract (index + 1) pending.size
  assignSelectedChildren pending (completed.push bubbleId)
    (remaining ++ childRemaining)

private partial def assignBubble (id : BubbleId) (focus : MVarId) :
    BubbleM Q (Array MVarId) := do
  let bubble ← getBubble id
  let goal ← bubble.goal.get
  let config ← getConfig
  trace[iaesop.search.bubble] "iaesop(bubble): replay bubble {bubble.id} for goal {goal.id}"
  let (normResult, normScript) ← liftM (m := ProofModeM) <|
    normalizeGoalMVar focus goal.depth config.maxNormIterations
      config.enableSimp? goal.unassignedMvars
      (recordScript := config.generateScript?)
  appendProofScript normScript
  match bubble.witness with
  | .normalization =>
      match normResult with
      | .proved => return #[]
      | _ => throwError
          "iaesop(bubble): replay normalization did not prove bubble {bubble.id}"
  | .rule rappRef children =>
      let normalizedFocus ← match normResult with
        | .proved => throwError
            "iaesop(bubble): replay normalization unexpectedly closed rule bubble {bubble.id}"
        | .changed goal => pure goal
        | .unchanged => pure focus
      let rapp ← rappRef.get
      let obunRef := rapp.children
      let obun ← obunRef.get
      let allSplits ← selectedSplits children
      let replaySplits :=
        if obun.kind.isManaged && obun.goals.size > 1 then allSplits else #[]
      trace[iaesop.search.bubble] "iaesop(bubble): replay \
        {rapp.appliedRule.info.builder} with {children.size} children and \
        {replaySplits.size} spatial splits"
      obunRef.modify fun obun =>
        obun.setState .proven |>.setFinalizedSpatialSplits replaySplits
      rappRef.modify fun rapp => rapp.setState .proven
      let preState ← liftM (m := ProofModeM) <|
        liftM (m := MetaM) saveState
      let replayGoals ← liftM (m := ProofModeM) <|
        rapp.appliedRule.info.builder.replay {
          goal := normalizedFocus
          rapp := ← rappRef.get
          config
        }
      recordRuleScript rappRef (← obunRef.get) preState normalizedFocus replayGoals config
      let isPureStop :=
        config.pureStop? && rapp.appliedRule.info.builder == .tactic .ipureIntro
      if isPureStop then
        return replayGoals
      if replayGoals.size != children.size then
        throwError s!"iaesop(bubble): replay produced {replayGoals.size} goals for \
          {children.size} selected child bubbles"
      let pending ← children.mapIdxM fun index childId => do
        let some childGoal := replayGoals[index]?
          | throwError "iaesop(bubble): replay child index is out of bounds"
        return (childId, childGoal)
      assignSelectedChildren pending #[] #[]

end

def replayProof (rootBubble : BubbleId) : BubbleM Q (Array MVarId) := do
  let rootRef ← liftM (m := Iris.ProofMode.Aesop.CoreM Q) getRootGoal
  let root ← rootRef.get
  root.preNormState.restore
  let remaining ← assignBubble rootBubble root.preNormGoal
  if (← getConfig).generateScript? then
    emitScriptSuggestion
  return remaining

end Iris.ProofMode.Aesop.Search.Bubble
