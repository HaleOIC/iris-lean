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
  deriving Nonempty

structure ObunData (GoalRef RappRef : Type) : Type where
  id : ObunId
  parent? : Option RappRef
  goals : Array GoalRef

  state : NodeState
  isIrrelevant : Bool

  kind : ObunKind
  scriptSteps? : Option (Array Script.LazyStep)
  metaState? : Option SavedState

  deriving Nonempty

structure RappData (GoalRef ObunRef : Type) : Type where
  id : RappId
  parent : GoalRef
  children : Array ObunRef

  state : NodeState
  isIrrelevant : Bool

  appliedRule : RegularRule
  successProbability : Percent
  scriptSteps? : Option (Array Script.LazyStep)

  -- [Note] we drop this field since rapp does not always have result in MVarId
  -- originalSubgoals : Array MVarId
  -- since we may not fillin the context split cases for each branch
  irisSubgoals : Array IrisGoal

  -- [TODO]:
  irisContext : Array (Array IrisHyp)

  metaState : SavedState
    -- This is the state *after* the rule was successfully applied, so the goal
    -- mvar is assigned in this state.
  introducedMVars : Std.HashSet MVarId
    -- Unassigned expression mvars introduced by this rapp. These are exactly
    -- the unassigned expr mvars that are declared in `metaState`, but not in
    -- the meta state of the parent rapp of `parent`.
  assignedMVars : Std.HashSet MVarId
    -- Expression mvars that were previously unassigned but were assigned by
    -- this rapp. These are exactly the expr mvars that (a) are declared and
    -- unassigned in the meta state of the parent rapp of `parent` and (b) are
    -- assigned in `metaState`.
  deriving Nonempty
