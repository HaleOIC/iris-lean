module

public meta import Iris.ProofMode.Aesop.Search.Shared.Queue
public meta import Iris.ProofMode.Aesop.Search.Shared.Configure
public meta import Iris.ProofMode.Aesop.Tree.TreeM
public meta import Iris.ProofMode.Aesop.Index.Basic
public meta import Iris.ProofMode.Aesop.Rule.Types.Info

public meta section

namespace Iris.ProofMode.Aesop

open Lean Std

initialize registerTraceClass `iaesop.tactic

namespace CoreM

structure Context where
  config : SearchConfig
  ruleIndex : Index RuleInfo
  -- later:
  -- statsRef : IO.Ref Stats

structure State (Q : Type) where
  iteration : Iteration
  queue : Q
  maxRuleApplicationDepthReached : Bool
  deriving Inhabited

end CoreM

/-- Shared search runtime: configuration, rule index, queue, and proof tree. -/
abbrev CoreM (Q : Type) [Queue Q] :=
  ReaderT CoreM.Context $ StateRefT (CoreM.State Q) $ StateRefT SearchTree ProofModeM

variable {Q : Type} [Queue Q]
namespace CoreM

instance : Monad (CoreM Q) :=
  { (inferInstance : Monad (CoreM Q)) with }

instance : MonadRef (CoreM Q) :=
  { (inferInstance : MonadRef (CoreM Q)) with }

instance : Inhabited (CoreM Q α) where
  default := failure

instance : MonadState (State Q) (CoreM Q) :=
  { (inferInstance : MonadStateOf (State Q) (CoreM Q)) with }

instance : MonadReader Context (CoreM Q) :=
  { (inferInstance : MonadReaderOf Context (CoreM Q)) with }

instance : MonadLift TreeM (CoreM Q) where
  monadLift x := do
    let ctx : TreeM.Context := { currentIteration := (← get).iteration }
    liftM <| ReaderT.run x ctx

protected def run (config : SearchConfig) (ruleIndex : Index RuleInfo)
    (goal : MVarId) (x : CoreM Q α) : ProofModeM (α × State Q × SearchTree) := do
  let ctx : Context := { config, ruleIndex }
  let tree ← mkInitialTree goal
  let init := {
    iteration := 0
    queue := ← Queue.init' (← tree.root.get).goals
    maxRuleApplicationDepthReached := false
  }
  let ((a, state), tree) ←
    (ReaderT.run x ctx).run init |>.run tree
  return (a, state, tree)

end CoreM

def getIteration : CoreM Q Nat :=
  return (← get).iteration

def incrementIteration : CoreM Q Unit :=
  modify λ s => { s with iteration := s.iteration + 1 }

def popGoal? : CoreM Q (Option GoalRef) := do
  let s ← get
  let (goals?, queue) ← Queue.popGoal s.queue
  set { s with queue }
  return goals?

def enqueueGoals (gs : Array GoalRef) : CoreM Q Unit := do
  let s ← get
  let queue ← Queue.addGoals s.queue gs
  set { s with queue }

def setMaxRuleApplicationDepthReached : CoreM Q Unit :=
  modify λ s => { s with maxRuleApplicationDepthReached := true }

def wasMaxRuleApplicationDepthReached : CoreM Q Bool :=
  return (← get).maxRuleApplicationDepthReached

end Aesop
