module

public import Iris.ProofMode.Aesop.Rule.Data
public import Iris.ProofMode.Aesop.Tree.Types
import Batteries.Lean.HashSet

public meta section

open Lean Lean.Meta Std
open Iris.ProofMode.Aesop
open Iris.ProofMode.Aesop.Util

namespace Iris.ProofMode.Aesop.Tree

structure GoalData (RappRef ObunRef : Type) : Type where
  id : GoalId
  parent : ObunRef
  children : GoalChildren RappRef ObunRef
  origin : GoalOrigin

  depth : Nat
  state : GoalState
  isIrrelevant : Bool

  -- Turn true because of reaching the search depth limit
  isForcedUnprovable : Bool
  preNormGoal : MVarId
  normalizationState : NormalizationState
  unassignedMvars : HashSet MVarId
  successProbability : Percent
  addedInIteration : Iteration
  -- 0 means the node has never been expanded
  lastExpandedInIteration : Iteration
  -- TODO: Not sure about regularRule
  failedRapps : Array RegularRule
  unsafeRulesSelected : Bool
  unsafeQueue : UnsafeQueue
  deriving Nonempty

structure ObunData (GoalRef RappRef : Type) : Type where
  id : ObunId
  parent : ObunParent GoalRef RappRef
  goals : Array GoalRef

  state : NodeState
  isIrrelevant : Bool

  kind : ObunKind
  scriptSteps? : Option (Array Script.LazyStep)
  metaState? : Option SavedState
  -- TODO: add some view from proof mode
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

  originalSubgoals : Array MVarId
  metaState : SavedState
    -- This is the state *after* the rule was successfully applied, so the goal
    -- mvar is assigned in this state.
  introducedMVars : HashSet MVarId
    -- Unassigned expression mvars introduced by this rapp. These are exactly
    -- the unassigned expr mvars that are declared in `metaState`, but not in
    -- the meta state of the parent rapp of `parent`.
  assignedMVars : HashSet MVarId
    -- Expression mvars that were previously unassigned but were assigned by
    -- this rapp. These are exactly the expr mvars that (a) are declared and
    -- unassigned in the meta state of the parent rapp of `parent` and (b) are
    -- assigned in `metaState`.
  deriving Nonempty
