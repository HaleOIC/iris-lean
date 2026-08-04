module

public meta import Iris.ProofMode.Aesop.Tree.Types

public section

namespace Iris.ProofMode.Aesop.Search.Bubble

open Lean Meta

/- Stable identity for a successful speculative proof candidate. -/
structure BubbleId where
  toNat : Nat
  deriving Inhabited, DecidableEq, BEq, Hashable, Repr

namespace BubbleId

protected def zero : BubbleId := ⟨0⟩

protected def succ : BubbleId → BubbleId
  | ⟨n⟩ => ⟨n + 1⟩

instance : ToString BubbleId where
  toString id := toString id.toNat

end BubbleId

/- Identity of one speculative group of metavariable-connected goals. -/
structure GroupId where
  toNat : Nat
  deriving Inhabited, DecidableEq, BEq, Hashable, Repr

namespace GroupId

protected def zero : GroupId := ⟨0⟩

protected def succ : GroupId → GroupId
  | ⟨n⟩ => ⟨n + 1⟩

instance : ToString GroupId where
  toString id := toString id.toNat

end GroupId

/- One metavariable assignment carried by a Bubble proof candidate.  This type
is kept in the data-only Bubble layer so an Obun can own its Bubble groups. -/
structure MetaAssignment where
  mvarId : MVarId
  value : Expr
  sourceState : SavedState

/- The first implementation treats resources as opaque comparable identities.
Integration will instantiate this with spatial Iris hypothesis identities. -/
structure Candidate (Resource : Type) where
  id : BubbleId
  childIndex : Nat
  consumed : Array Resource
  pre : Option BubbleId := none
  constituents : Array BubbleId := #[]
  deriving Inhabited

abbrev CombinationKey := Array BubbleId

inductive ResourcePolicy
  | disjoint
  | shared
  deriving Inhabited, BEq

structure Combination (Resource : Type) where
  selected : Array (Candidate Resource)
  consumed : Array Resource
  deriving Inhabited

structure Platform (Resource : Type) where
  childCount : Nat
  resourcePolicy : ResourcePolicy := .disjoint
  byChild : Array (Array (Candidate Resource))
  emitted : Array CombinationKey := #[]
  deriving Inhabited

namespace Platform

def empty (childCount : Nat) (resourcePolicy : ResourcePolicy := .disjoint) :
    Platform Resource :=
  {
    childCount
    resourcePolicy
    byChild := (List.replicate childCount #[]).toArray
  }

end Platform

structure GroupMemberData (GoalRef : Type) where
  originalIndex : Nat
  goal : GoalRef

/- One Bubble alternative inside an Obun.  Initial groups partition the
Obun's committed goals by shared unassigned metavariables.  Residual groups
remain in the same Obun and point to the group from which they were refined. -/
structure GoalGroupData (GoalRef : Type) where
  id : GroupId
  rootIndex : Nat
  members : Array (GroupMemberData GoalRef)
  preGroup? : Option GroupId := none
  prefixProofs : Array (Nat × BubbleId) := #[]
  prefixConsumed : Array IrisHyp := #[]
  prefixMetaInfo : Array MetaAssignment := #[]
  externalPrefix? : Option BubbleId := none
  externalAncestors : Array BubbleId := #[]
  externalConsumed : Array IrisHyp := #[]
  externalMetaInfo : Array MetaAssignment := #[]
  platform : Platform IrisHyp

end Iris.ProofMode.Aesop.Search.Bubble
