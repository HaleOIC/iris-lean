module

public meta import Iris.ProofMode.Aesop.Search.Queue
public meta import Iris.ProofMode.Aesop.Search.Configure
public meta import Iris.ProofMode.Aesop.Tree.TreeM

public meta section

namespace Iris.ProofMode.Aesop

open Lean Std

namespace SearchM

structure Context where
  config : SearchConfig
  -- later:
  -- ruleSet : RuleSet
  -- statsRef : IO.Ref Stats

structure State (Q : Type) where
  iteration : Iteration
  queue : Q
  maxRuleApplicationDepthReached : Bool
  deriving Inhabited

end SearchM

abbrev SearchM (Q : Type) [Queue Q] :=
  ReaderT SearchM.Context $ StateRefT (SearchM.State Q) $ StateRefT SearchTree ProofModeM

variable {Q : Type} [Queue Q]
namespace SearchM

instance : Monad (SearchM Q) :=
  { (inferInstance : Monad (SearchM Q)) with }

instance : MonadRef (SearchM Q) :=
  { (inferInstance : MonadRef (SearchM Q)) with }

instance : Inhabited (SearchM Q α) where
  default := failure

instance : MonadState (State Q) (SearchM Q) :=
  { (inferInstance : MonadStateOf (State Q) (SearchM Q)) with }

instance : MonadReader Context (SearchM Q) :=
  { (inferInstance : MonadReaderOf Context (SearchM Q)) with }

instance : MonadLift TreeM (SearchM Q) where
  monadLift x := do
    let ctx : TreeM.Context := { currentIteration := (← get).iteration }
    liftM <| ReaderT.run x ctx

-- TODO: add ruleset as parameter
protected def run (config : SearchConfig) (goal : MVarId)
    (x : SearchM Q α) : ProofModeM (α × State Q × SearchTree) := do
  let ctx : Context := { config := config }
  let tree ← mkInitialTree goal
  let init := {
    iteration := 0
    queue := ← Queue.init' (← tree.root.get).goals
    maxRuleApplicationDepthReached := false
  }
  let ((a, state), tree) ←
    (ReaderT.run x ctx).run init |>.run tree
  return (a, state, tree)

end SearchM

def getIteration : SearchM Q Nat :=
  return (← get).iteration

def incrementIteration : SearchM Q Unit :=
  modify λ s => { s with iteration := s.iteration + 1 }

def popGoal? : SearchM Q (Option GoalRef) := do
  let s ← get
  let (goals?, queue) ← Queue.popGoal s.queue
  set { s with queue }
  return goals?

def enqueueGoals (gs : Array GoalRef) : SearchM Q Unit := do
  let s ← get
  let queue ← Queue.addGoals s.queue gs
  set { s with queue }

def setMaxRuleApplicationDepthReached : SearchM Q Unit :=
  modify λ s => { s with maxRuleApplicationDepthReached := true }

def wasMaxRuleApplicationDepthReached : SearchM Q Bool :=
  return (← get).maxRuleApplicationDepthReached

end Aesop
