module

public meta import Iris.ProofMode.Aesop.Tree.Basic
public meta import Iris.ProofMode.ProofModeM

public meta section

open Lean Lean.Meta

namespace Iris.ProofMode.Aesop

structure SearchTree where
  root : ObunRef
  rootMetaState : SavedState
  nextGoalId : GoalId
  nextRappId : RappId
  nextObunId : ObunId

def mkInitialTree (root : MVarId) : ProofModeM SearchTree := do
  -- sanity check: [iaesop] only works in iris proof-mode
  let goalType ← root.withContext do
    instantiateMVars (← root.getType)
  let some _ := parseIrisGoal? goalType
    | throwError "iaesop: root goal is not an Iris proof-mode goal"

  let rootMetaState ← liftM Meta.saveState
  let rootObunRef ← IO.mkRef $ Obun.mk {
    id := .zero
    parent? := none
    goals := #[]
    isIrrelevant := false
    state := .unknown
    kind := .plain
    scriptSteps? := none
    metaState? := some rootMetaState
  }
  let rootGoalRef ← IO.mkRef $ Goal.mk {
    id := .zero
    mask := .empty 0
    parent := rootObunRef
    children := #[]
    origin := .subgoal
    depth := 0
    state := .unknown
    isIrrelevant := false
    isForcedUnprovable := false
    preNormGoal := root
    preNormState := rootMetaState
    normalizationState := .notNormal
    unassignedMvars := ← root.getMVarDependencies
    successProbability := .hundred
    addedInIteration := 1
    lastExpandedInIteration := 1
    rulesQueue := {}
    appendiedGoalId := #[]
  }

  -- Patch Obun's goals
  rootObunRef.modify λ o => o.setGoals #[rootGoalRef]
  return {
    root := rootObunRef
    rootMetaState
    nextGoalId := .one
    nextRappId := .zero
    nextObunId := .one
  }

namespace TreeM

structure Context where
  currentIteration : Iteration

end TreeM

abbrev TreeM := ReaderT TreeM.Context $ StateRefT SearchTree ProofModeM

namespace TreeM

instance : Monad TreeM :=
  { (inferInstance : Monad TreeM) with }

instance : Inhabited (TreeM α) where
  default := failure

def run (ctx : Context) (tree : SearchTree) (x : TreeM α) :
    ProofModeM (α × SearchTree) :=
  ReaderT.run x ctx |>.run tree

end TreeM

def getRootObun : TreeM ObunRef :=
  return (← get).root

def getRootMetaState : TreeM SavedState :=
  return (← get).rootMetaState

def getRootGoals : TreeM (Array GoalRef) := do
  return (← (← getRootObun).get).goals

def getRootGoal : TreeM GoalRef := do
  let goals ← getRootGoals
  if h : goals.size = 1 then
    return goals[0]
  else
    throwError "iaesop: expected exactly one root goal, found {goals.size}"

def getRootMVar : TreeM MVarId := do
  return (← (← getRootGoal).get).preNormGoal

def getAndIncrementNextGoalId : TreeM GoalId := do
  modifyGetThe SearchTree λ t =>
    let id := t.nextGoalId
    (id, { t with nextGoalId := id.succ })

def getAndIncrementNextRappId : TreeM RappId := do
  modifyGetThe SearchTree λ t =>
    let id := t.nextRappId
    (id, { t with nextRappId := id.succ })

def getAndIncrementNextObunId : TreeM ObunId := do
  modifyGetThe SearchTree λ t =>
    let id := t.nextObunId
    (id, { t with nextObunId := id.succ })

end Iris.ProofMode.Aesop
