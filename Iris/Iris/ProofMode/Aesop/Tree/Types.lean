module

public meta import Lean.Meta.Basic
public import Iris.ProofMode.Aesop.Rule.Name
public import Iris.ProofMode.Aesop.Script.Basic

public meta section

open Lean Lean.Meta
open Iris.ProofMode.Aesop

namespace Iris.ProofMode.Aesop.Tree

abbrev Iteration := Nat

structure GoalId where
  toNat : Nat
  deriving Inhabited, DecidableEq, BEq, Hashable, Repr

namespace GoalId

protected def zero : GoalId := ⟨0⟩

protected def one : GoalId := ⟨1⟩

protected def succ : GoalId → GoalId
  | ⟨n⟩ => ⟨n + 1⟩

instance : LT GoalId where
  lt n m := n.toNat < m.toNat

instance : DecidableRel (α := GoalId) (· < ·) :=
  λ n m => inferInstanceAs (Decidable (n.toNat < m.toNat))

instance : ToString GoalId where
  toString n := toString n.toNat

end GoalId

structure RappId where
  toNat : Nat
  deriving Inhabited, DecidableEq, BEq, Hashable, Repr

namespace RappId

protected def zero : RappId := ⟨0⟩

protected def one : RappId := ⟨1⟩

protected def succ : RappId → RappId
  | ⟨n⟩ => ⟨n + 1⟩

instance : LT RappId where
  lt n m := n.toNat < m.toNat

instance : DecidableRel (α := RappId) (· < ·) :=
  λ n m => inferInstanceAs $ Decidable (n.toNat < m.toNat)

instance : ToString RappId where
  toString n := toString n.toNat

end RappId

structure ObunId where
  toNat : Nat
  deriving Inhabited, DecidableEq, BEq, Hashable, Repr

namespace ObunId

protected def zero : ObunId := ⟨0⟩

protected def one : ObunId := ⟨1⟩

protected def succ : ObunId → ObunId
  | ⟨n⟩ => ⟨n + 1⟩

instance : LT ObunId where
  lt n m := n.toNat < m.toNat

instance : DecidableRel (α := ObunId) (· < ·) :=
  λ n m => inferInstanceAs $ Decidable (n.toNat < m.toNat)

instance : ToString ObunId where
  toString n := toString n.toNat

end ObunId

/--
- `proven`: the node is proven
- `unprovable`: the node is unprovable
- `unknown`: neither of the above (default)
-/
inductive NodeState
  | unknown
  | proven
  | unprovable
  deriving Inhabited, BEq

namespace NodeState

instance : ToString NodeState where
  toString
    | unknown => "unknown"
    | proven => "proven"
    | unprovable => "unprovable"

def isUnknown : NodeState → Bool
  | unknown => true
  | _ => false

def isProven : NodeState → Bool
  | proven => true
  | _ => false

def isUnprovable : NodeState → Bool
  | unprovable => true
  | _ => false

def isIrrelevant : NodeState → Bool
  | proven => true
  | unprovable => true
  | unknown => false

end NodeState

inductive GoalState
  | unknown
  | provenByRuleApplication
  | provenByNormalization
  | unprovable
  deriving Inhabited, BEq

namespace GoalState

instance : ToString GoalState where
  toString
    | unknown => "unknown"
    | provenByRuleApplication => "provenByRuleApplication"
    | provenByNormalization =>  "provenByNormalization"
    | unprovable => "unprovable"

def isProvenByRuleApplication : GoalState → Bool
  | provenByRuleApplication => true
  | _ => false

def isProvenByNormalization : GoalState → Bool
  | provenByNormalization => true
  | _ => false

def isProven : GoalState → Bool
  | provenByRuleApplication => true
  | provenByNormalization => true
  | _ => false

def isUnprovable : GoalState → Bool
  | unprovable => true
  | _ => false

def isUnknown : GoalState → Bool
  | unknown => true
  | _ => false

def toNodeState : GoalState → NodeState
  | unknown => NodeState.unknown
  | provenByRuleApplication => NodeState.proven
  | provenByNormalization => NodeState.proven
  | unprovable => NodeState.unprovable

def isIrrelevant (s : GoalState) : Bool :=
  s.toNodeState.isIrrelevant

end GoalState

inductive NormalizationState
  | notNormal
  | normal (postGoal : MVarId) (postState : Meta.SavedState)
      (script : Array (Rule.DisplayRuleId × Option (Array Script.LazyStep)))
  | provenByNorm (postState : Meta.SavedState)
      (script : Array (Rule.DisplayRuleId × Option (Array Script.LazyStep)))
  deriving Inhabited

namespace NormalizationState

def isNormal : NormalizationState → Bool
  | notNormal => false
  | normal .. => true
  | provenByNorm .. => true

def isProvenByNorm : NormalizationState → Bool
  | notNormal .. => false
  | normal .. => false
  | provenByNorm .. => true

def normalizedGoal? : NormalizationState → Option MVarId
  | notNormal .. | provenByNorm .. => none
  | normal (postGoal := g) .. => g

end NormalizationState

-- TODO: Unclear about the presence of [droppedMVar]
inductive GoalOrigin
  | subgoal
  | copied («from» : GoalId) (rep : GoalId)
  | droppedMVar
  deriving Inhabited, BEq

namespace GoalOrigin

def originalGoalId? : GoalOrigin → Option GoalId
  | .copied _ rep => some rep
  | _ => none

instance : ToString GoalOrigin where
  toString
    | .subgoal => "subgoal"
    | .copied src rep => s!"copy of {src}, originally {rep}"
    | .droppedMVar => "dropped mvar"

end GoalOrigin

inductive ObunKind
  | plain
  | managed
  deriving Inhabited, BEq

namespace ObunKind

def isPlain : ObunKind → Bool
  | plain => true
  | _ => false

def isManaged : ObunKind → Bool
  | managed => true
  | _ => false

end ObunKind

end Tree
