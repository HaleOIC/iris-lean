module

public meta import Lean.Meta.Basic
public import Iris.ProofMode.Expr
public import Iris.ProofMode.Aesop.Rule.Types.Name
public import Iris.ProofMode.Aesop.Script.Basic

public meta section

open Lean Meta
open Iris.ProofMode.Aesop

namespace Iris.ProofMode.Aesop

-- Only record the spatial iris-hypothesis
structure IrisHyp where
  name : Name
  ivar : IVarId
  deriving Inhabited, BEq

namespace IrisHyp

instance : ToString IrisHyp where
  toString := (·.name.toString)

end IrisHyp

/- Record the concrete hypothesis used by a rule application. -/
inductive AppliedHyp where
  | spatial (hyp : IrisHyp)
  | intuitionistic (hyp : IrisHyp)
  | lean (userName : Name) (fvarId : FVarId)

namespace AppliedHyp

instance : ToString AppliedHyp where
  toString
    | spatial hyp => s!"spatial {hyp}"
    | intuitionistic hyp => s!"intuitionistic {hyp}"
    | lean userName _ => s!"lean {userName}"

def consumedSpatialHyp? : AppliedHyp → Option IrisHyp
  | .spatial hyp => some hyp
  | _ => none

end AppliedHyp

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
  | locallySettled
  | proven
  | unprovable
  deriving Inhabited, BEq

namespace NodeState

instance : ToString NodeState where
  toString
    | unknown => "unknown"
    | locallySettled => "locallySettled"
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

def isLocallySettled : NodeState → Bool
  | locallySettled => true
  | _ => false

def isIrrelevant : NodeState → Bool
  | proven => true
  | locallySettled => false
  | unprovable => true
  | unknown => false

end NodeState

inductive GoalState
  | unknown
  | provenByRuleApplication
  | provenByNormalization
  | locallySettled
  | unprovable
  deriving Inhabited, BEq

namespace GoalState

instance : ToString GoalState where
  toString
    | unknown => "unknown"
    | provenByRuleApplication => "provenByRuleApplication"
    | provenByNormalization =>  "provenByNormalization"
    | locallySettled => "locallySettled"
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

def isLocallySettled : GoalState → Bool
  | locallySettled => true
  | _ => false

def toNodeState : GoalState → NodeState
  | unknown => NodeState.unknown
  | provenByRuleApplication => NodeState.proven
  | provenByNormalization => NodeState.proven
  | locallySettled => NodeState.locallySettled
  | unprovable => NodeState.unprovable

def isIrrelevant (s : GoalState) : Bool :=
  s.toNodeState.isIrrelevant

end GoalState

inductive NormalizationState
  | notNormal
  | normal (postGoal : MVarId) (postState : Meta.SavedState)
      (generatedSpatialHyps : Array IrisHyp) (usedSpatialHyps : Array IrisHyp)
      (script : Array (DisplayRuleId × Option (Array Script.LazyStep)))
  | provenByNorm (postState : Meta.SavedState)
      (generatedSpatialHyps : Array IrisHyp) (usedSpatialHyps : Array IrisHyp)
      (script : Array (DisplayRuleId × Option (Array Script.LazyStep)))
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

def generatedSpatialHyps : NormalizationState → Array IrisHyp
  | notNormal => #[]
  | normal (generatedSpatialHyps := hyps) .. => hyps
  | provenByNorm (generatedSpatialHyps := hyps) .. => hyps

def usedSpatialHyps : NormalizationState → Array IrisHyp
  | notNormal => #[]
  | normal (usedSpatialHyps := hyps) .. => hyps
  | provenByNorm (usedSpatialHyps := hyps) .. => hyps

end NormalizationState

-- TODO: Unclear about the presence of [droppedMVar]
inductive GoalOrigin
  | subgoal
  | copied («from» : GoalId)
  | droppedMVar
  deriving Inhabited, BEq

namespace GoalOrigin

instance : ToString GoalOrigin where
  toString
    | .subgoal => "subgoal"
    | .copied src => s!"copy of {src}"
    | .droppedMVar => "dropped mvar"

end GoalOrigin

/--
  [.plain] indicates that the current obligation bundle does not manage context.
  In this mode, `localSettled` can be claimed only after all subgoals have been
  marked as proven.

  [.managed] indicates that the current obligation bundle manages context.
  In this mode, `localSettled` can be claimed as soon as the progress bar of
  at least one subgoal is complete.
-/
inductive ObunKind
  | plain
  | managed
  | duplicated
  | inherited (source : ObunId) (diff? : Bool)
  deriving Inhabited, BEq

namespace ObunKind

instance : ToString ObunKind where
  toString
    | plain => "plain"
    | managed => "managed"
    | duplicated => "duplicated"
    | inherited source diff? => s!"inherited from {source}" ++
      if diff? then "(managed)" else "(duplicated)"

def isPlain : ObunKind → Bool
  | plain => true
  | _ => false

def isManaged : ObunKind → Bool
  | managed => true
  | _ => false

def isDuplicated : ObunKind → Bool
  | duplicated => true
  | _ => false

def isInherited : ObunKind → Bool
  | inherited .. => true
  | _ => false

def source? : ObunKind → Option ObunId
  | inherited source _ => some source
  | _ => none

end ObunKind

structure CaseId where
  toNat : Nat
  deriving Inhabited, DecidableEq, BEq, Hashable, Repr

namespace CaseId

protected def zero : CaseId :=
  ⟨0⟩

def ofNat (index : Nat) : CaseId :=
  ⟨index⟩

def index? (id : CaseId) : Nat :=
  id.toNat

instance : ToString CaseId where
  toString id := toString id.toNat

end CaseId
