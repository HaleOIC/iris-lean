module

public meta import Iris.ProofMode.Aesop.Search.Queue
public meta import Iris.ProofMode.Aesop.Tree.TreeM

public meta section

open Lean Std
open Iris.ProofMode.Aesop.Tree
open Iris.ProofMode.Aesop.Util

namespace Iris.ProofMode.Aesop.Search

structure SearchConfig where
  traceScript : Bool := false
  maxSteps : Nat := 200

namespace SearchM

structure Context where
  config : SearchConfig
  -- later:
  -- ruleSet : RuleSet
  -- statsRef : IO.Ref Stats

structure State where
  iteration : Iteration := 0
  queue : BestFirstQueue
  stuck : Array MVarId := #[]

end SearchM

abbrev SearchM :=
  ReaderT SearchM.Context $
    StateRefT SearchM.State $
      StateRefT SearchTree ProofModeM

namespace SearchM

instance : Monad SearchM :=
  { (inferInstance : Monad SearchM) with }

instance : MonadRef SearchM :=
  { (inferInstance : MonadRef SearchM) with }

instance : Inhabited (SearchM α) where
  default := failure

instance : MonadState State SearchM :=
  { (inferInstance : MonadStateOf State SearchM) with }

instance : MonadReader Context SearchM :=
  { (inferInstance : MonadReaderOf Context SearchM) with }

instance : MonadLift TreeM SearchM where
  monadLift x := do
    let ctx : TreeM.Context :=
      { currentIteration := (← get).iteration }
    liftM <| ReaderT.run x ctx

protected def run (config : SearchConfig) (root : MVarId) (x : SearchM α) :
    ProofModeM (α × State × SearchTree) := do
  let ctx : Context := { config := config }
  let tree ← mkInitialTree root
  let rootGoals := (← tree.root.get).goals
  let queue ← Queue.init' rootGoals
  let init : State := { queue }
  let ((a, state), tree) ← (ReaderT.run x ctx).run init |>.run tree
  return (a, state, tree)

def getConfig : SearchM SearchConfig :=
  return (← read).config

def getIteration : SearchM Nat :=
  return (← get).iteration

def incrementIteration : SearchM Unit :=
  modify λ s => { s with iteration := s.iteration + 1 }

private def mkQueuedGoalRef (mvar : MVarId) : SearchM GoalRef := do
  let parent ← getRootObun
  let id ← getAndIncrementNextGoalId
  let iteration ← getIteration
  let unassignedMvars ← liftM <| mvar.withContext do
    mvar.getMVarDependencies
  let gref ← IO.mkRef $ Goal.mk {
    id
    parent
    children := GoalChildren.none
    origin := GoalOrigin.subgoal
    depth := 0
    state := GoalState.unknown
    isIrrelevant := false
    isForcedUnprovable := false
    preNormGoal := mvar
    normalizationState := NormalizationState.notNormal
    unassignedMvars
    successProbability := Percent.hundred
    addedInIteration := iteration
    lastExpandedInIteration := 0
    failedRapps := #[]
    unsafeRulesSelected := false
    unsafeQueue := #[]
  }
  parent.modify fun o => o.setGoals ((o.goals).push gref)
  return gref

def popGoal? : SearchM (Option MVarId) := do
  let s ← get
  let (gref?, queue) ← Queue.popGoal s.queue
  set { s with queue }
  match gref? with
  | none => return none
  | some gref => do
    let g ← gref.get
    return some g.preNormGoal

def enqueueGoals (goals : Array MVarId) : SearchM Unit := do
  let grefs ← goals.mapM mkQueuedGoalRef
  let s ← get
  let queue ← Queue.addGoals s.queue grefs
  set { s with queue }

def addStuck (goal : MVarId) : SearchM Unit :=
  modify λ s => { s with stuck := s.stuck.push goal }

def remainingGoals : SearchM (Array MVarId) := do
  let s ← get
  let queued ← s.queue.toArray.mapM fun ag => do
    let g ← ag.goal.get
    return g.preNormGoal
  return s.stuck ++ queued

end SearchM

end Iris.ProofMode.Aesop.Search
