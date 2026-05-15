module

public import Iris.ProofMode.Expr
public import Iris.ProofMode.Aesop.Rule.Types.Match
public import Iris.ProofMode.Aesop.Tree.Types
public import Iris.ProofMode.Aesop.Util.Basic
public meta section

namespace Iris.ProofMode.Aesop

open Lean Lean.Meta Std
open Iris.ProofMode.Aesop

structure GoalData (RappRef ObunRef : Type) : Type where
  id : GoalId
  mask : ProgressMask
  parent : ObunRef
  children : Array RappRef
  origin : GoalOrigin

  depth : Nat
  state : GoalState
  isIrrelevant : Bool

  -- Turn true because of reaching the search depth limit
  isForcedUnprovable : Bool
  preNormGoal : MVarId
  preNormState : SavedState
  normalizationState : NormalizationState

  unassignedMvars : Std.HashSet MVarId
  successProbability : Percent
  addedInIteration : Iteration
  lastExpandedInIteration : Iteration

  rulesQueue : RuleQueue
  appendiedGoalId : Array GoalId
  deriving Nonempty

structure ObunData (GoalRef RappRef : Type) : Type where
  id : ObunId
  parent? : Option RappRef
  goals : Array GoalRef

  state : NodeState
  isIrrelevant : Bool

  metaState? : Option SavedState
  scriptSteps? : Option (Array Script.LazyStep)

  /- Iris context-management data -/

  /- Indicates whether this obligation bundle uses context-management mode. -/
  kind : ObunKind

  /- Indicate which goal -/

  deriving Nonempty

structure RappData (GoalRef ObunRef : Type) : Type where
  id : RappId
  parent : GoalRef
  children : ObunRef

  state : NodeState
  isIrrelevant : Bool

  appliedRule : RegularRule
  successProbability : Percent
  scriptSteps? : Option (Array Script.LazyStep)

  /- ### Iris context-management data -/

  /- Full-context Iris subgoal templates produced by this rule application -/
  fullContextIrisSubgoals : Array IrisGoal
  /- Spatial Iris hypothesis consumed by this rule application, if any -/
  consumedSpatialHyp? : Option IrisHyp
  /- Lean hypothesis consumed by this rule application, if any -/
  consumedLeanHyp? : Option FVarId
  /- Finalized spatial-context split assignments, ordered by split case -/
  finalizedSpatialSplits : Array (Array IrisHyp)

  /- ### Lean context-related data -/

  /- Meta state immediately after the rule application succeeds. -/
  metaState : SavedState
  /- Expression metavariables introduced by this rule application. -/
  introducedMVars : Std.HashSet MVarId
  /- Existing expression metavariables assigned by this rule application. -/
  assignedMVars : Std.HashSet MVarId

  deriving Nonempty

end Aesop
