module

public meta import Iris.ProofMode.Aesop.Search.Shared.CoreM
public meta import Iris.ProofMode.Aesop.Search.Bubble.Platform

public meta section

namespace Iris.ProofMode.Aesop.Search.Bubble

open Lean Meta
open Iris.ProofMode.Aesop

inductive ProofWitness where
  | normalization
  | rule (rapp : RappRef) (children : Array BubbleId)
  deriving Inhabited

structure ProofBubble where
  id : BubbleId
  goal : GoalRef
  consumed : Array IrisHyp
  metaInfo : Array MetaAssignment
  pre : Option BubbleId := none
  witness : ProofWitness

abbrev GroupMember := GroupMemberData GoalRef
abbrev GoalGroup := GoalGroupData GoalRef

structure GoalGroupLocation where
  goalId : GoalId
  groupId : GroupId
  memberIndex : Nat
  deriving Inhabited

/- A completed group is an atomic candidate at the outer linear platform.
Its ID shares the global bubble-ID supply but is stored separately from proof
bubbles. -/
structure GroupCompletion where
  id : BubbleId
  obunId : ObunId
  groupId : GroupId
  rootIndex : Nat
  proofs : Array (Nat × BubbleId)
  consumed : Array IrisHyp
  metaInfo : Array MetaAssignment
  externalPrefix? : Option BubbleId
  externalAncestors : Array BubbleId
  reservedConsumed : Array IrisHyp
  representative : BubbleId
  deriving Inhabited

structure SpawnedGroup where
  obunId : ObunId
  rootIndex : Nat
  trigger : BubbleId
  preGroup : GroupId
  deriving Inhabited

structure ResidualEntry where
  goalId : GoalId
  obunId : ObunId
  childIndex : Nat
  pre : BubbleId
  deriving Inhabited

structure State where
  nextBubbleId : BubbleId := .zero
  nextGroupId : GroupId := .zero
  bubbles : Array ProofBubble := #[]
  /- Registry used only to revisit stalled platforms.  Group and platform data
  themselves are owned by the referenced Obuns. -/
  platformObuns : Array (ObunId × ObunRef) := #[]
  groupCompletions : Array GroupCompletion := #[]
  spawnedGroups : Array SpawnedGroup := #[]
  residuals : Array ResidualEntry := #[]
  /- Goals whose finite rule queue has been consumed.  The shared `Goal`
  stores an empty queue both before rule selection and after exhaustion, so
  bubble search must remember the distinction or it will query the index and
  retry the same rules forever. -/
  exhaustedGoals : Array GoalId := #[]
  proofScript : Script.UScript := #[]
  rootSolution? : Option BubbleId := none
  deriving Inhabited

/-- Bubble-local state layered over the shared search runtime. -/
abbrev BubbleM (Q : Type) [Queue Q] :=
  StateRefT State (Iris.ProofMode.Aesop.CoreM Q)

variable {Q : Type} [Queue Q]

def freshBubbleId : BubbleM Q BubbleId := do
  modifyGetThe State fun state =>
    (state.nextBubbleId, { state with nextBubbleId := state.nextBubbleId.succ })

def freshGroupId : BubbleM Q GroupId := do
  modifyGetThe State fun state =>
    (state.nextGroupId, { state with nextGroupId := state.nextGroupId.succ })

def registerBubble (goal : GoalRef) (consumed : Array IrisHyp)
    (metaInfo : Array MetaAssignment)
    (witness : ProofWitness) (pre : Option BubbleId := none) :
    BubbleM Q ProofBubble := do
  let bubble := { id := ← freshBubbleId, goal, consumed, metaInfo, pre, witness }
  modifyThe State fun state => { state with bubbles := state.bubbles.push bubble }
  return bubble

def getBubble (id : BubbleId) : BubbleM Q ProofBubble := do
  let some bubble := (← getThe State).bubbles.find? fun bubble => bubble.id == id
    | throwError "iaesop(bubble): unknown bubble {id}"
  return bubble

def getGroup (obunRef : ObunRef) (id : GroupId) : BubbleM Q GoalGroup := do
  let some group := (← obunRef.get).bubbleGroups.find? fun group => group.id == id
    | throwError "iaesop(bubble): unknown goal group {id}"
  return group

def setGroup (obunRef : ObunRef) (group : GoalGroup) : BubbleM Q Unit :=
  obunRef.modify fun obun =>
    let groups := obun.bubbleGroups
    match groups.findIdx? fun old => old.id == group.id with
    | some index => obun.setBubbleGroups (groups.set! index group)
    | none => obun.setBubbleGroups (groups.push group)

def registerPlatformObun (obunRef : ObunRef) : BubbleM Q Unit := do
  let obunId := (← obunRef.get).id
  modifyThe State fun state =>
    if state.platformObuns.any fun old => old.1 == obunId then state
    else { state with platformObuns := state.platformObuns.push (obunId, obunRef) }

def getGroupCompletion (id : BubbleId) : BubbleM Q GroupCompletion := do
  let some completion := (← getThe State).groupCompletions.find? fun entry =>
      entry.id == id
    | throwError "iaesop(bubble): unknown group completion {id}"
  return completion

def getRootSolution? : BubbleM Q (Option BubbleId) :=
  return (← getThe State).rootSolution?

def setRootSolution (id : BubbleId) : BubbleM Q Unit :=
  modifyThe State fun state =>
    if state.rootSolution?.isSome then state else { state with rootSolution? := some id }

def isGoalExhausted (goalId : GoalId) : BubbleM Q Bool :=
  return (← getThe State).exhaustedGoals.contains goalId

def markGoalExhausted (goalId : GoalId) : BubbleM Q Unit :=
  modifyThe State fun state =>
    if state.exhaustedGoals.contains goalId then state
    else { state with exhaustedGoals := state.exhaustedGoals.push goalId }

def appendProofScript (steps : Script.UScript) : BubbleM Q Unit :=
  unless steps.isEmpty do
    modifyThe State fun state =>
      { state with proofScript := state.proofScript ++ steps }

def getProofScript : BubbleM Q Script.UScript :=
  return (← getThe State).proofScript

def goalPre? (goalId : GoalId) : BubbleM Q (Option BubbleId) :=
  return (← getThe State).residuals.find? (fun entry => entry.goalId == goalId)
    |>.map (·.pre)

def recordResidual (entry : ResidualEntry) : BubbleM Q Unit :=
  modifyThe State fun state => {
    state with
    residuals := state.residuals.push entry
  }

end Iris.ProofMode.Aesop.Search.Bubble
