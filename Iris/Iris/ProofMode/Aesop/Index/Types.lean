module

public import Batteries.Lean.Meta.DiscrTree
public import Batteries.Lean.HashSet
public import Iris.ProofMode.Expr

public meta section

open Lean Meta Std
open Iris.ProofMode

namespace Iris.ProofMode.Aesop

/-- Configuration used to turn Iris proposition expressions into discrimination
tree paths. Keep this consistent between rule registration and rule selection. -/
def indexConfig : ConfigWithKey :=
  ({ proj := .no, transparency := .reducible : Config }).toConfigWithKey

def mkIndexPath (e : Expr) : MetaM (Array DiscrTree.Key) :=
  withConfigWithKey indexConfig <| DiscrTree.mkPath e

def getUnify (tree : DiscrTree α) (e : Expr) : MetaM (Array α) :=
  withConfigWithKey indexConfig <| tree.getUnify e

/-- Describes which part of an Iris proof-mode goal should select a rule. -/
inductive IndexingMode
  | unindexed
  | fullGoal (keys : Array DiscrTree.Key)
  | target (keys : Array DiscrTree.Key)
  | irisHyps (keys : Array DiscrTree.Key)
  | leanHyps (keys : Array DiscrTree.Key)
  | or (modes : Array IndexingMode)
  deriving Inhabited

namespace IndexingMode

protected partial def format : IndexingMode → Format
  | unindexed => "unindexed"
  | fullGoal keys => f!"fullGoal {keys}"
  | target keys => f!"target {keys}"
  | irisHyps keys => f!"irisHyps {keys}"
  | leanHyps keys => f!"leanHyps {keys}"
  | or modes => f!"or {modes.map IndexingMode.format}"

instance : ToFormat IndexingMode :=
  ⟨IndexingMode.format⟩

def fullGoalMatching (pattern : Expr) : MetaM IndexingMode :=
  return .fullGoal (← mkIndexPath pattern)

def targetMatching (pattern : Expr) : MetaM IndexingMode :=
  return .target (← mkIndexPath pattern)

def irisHypsMatching (pattern : Expr) : MetaM IndexingMode :=
  return .irisHyps (← mkIndexPath pattern)

def leanHypsMatching (pattern : Expr) : MetaM IndexingMode :=
  return .leanHyps (← mkIndexPath pattern)

end IndexingMode

inductive IndexMatchLocation
  | none
  | fullGoal
  | target
  | irisHyp (userName : Name) (ivarId : IVarId) (persistent : Bool)
  | leanHyp (userName : Name) (fvarId : FVarId)
  deriving Inhabited, BEq, Hashable

namespace IndexMatchLocation

instance : ToMessageData IndexMatchLocation where
  toMessageData
    | none => "none"
    | fullGoal => "full goal"
    | target => "target"
    | irisHyp userName ivarId p =>
      m!"Iris hypothesis {userName} {ivarId.name} {if p then "(Persistent)" else ""}"
    | leanHyp userName fvarId =>
      m!"Lean hypothesis {userName} {fvarId.name}"

end IndexMatchLocation

-- [TODO] Support rule pattern match instantiation later
-- structure RulePatternSubst where
--   exprs : Array Expr := #[]
--   levels : Array Level := #[]
--   deriving Inhabited

/-- A rule selected by the index -/
structure IndexMatchResult (α : Type) where
  rule : α
  locations : HashSet IndexMatchLocation := {}
  -- [Note] See above TODO
  -- patternSubsts? : Option (Array RulePatternSubst) := none
  deriving Inhabited

namespace IndexMatchResult

instance [Ord α] : Ord (IndexMatchResult α) where
  compare r s := compare r.rule s.rule

instance [Ord α] : LT (IndexMatchResult α) :=
  ltOfOrd

instance [ToMessageData α] : ToMessageData (IndexMatchResult α) where
  toMessageData result := toMessageData result.rule

end IndexMatchResult

end Iris.ProofMode.Aesop
