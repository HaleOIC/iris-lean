module

public meta import Iris.ProofMode.Aesop.Search.SearchM
public meta import Iris.ProofMode.Aesop.Rule.Types.Info
public meta import Iris.ProofMode.Aesop.Rule.Types.Match
public meta import Iris.ProofMode.Aesop.Tree.Basic

public meta section

namespace Iris.ProofMode.Aesop

open Lean Meta Std

inductive RuleRunnerDescr where
  | identity
  | applyHyps
  | ipureIntro
  | imodIntro
  | imod
  | iexact
  | custom
  deriving Inhabited, BEq, Hashable, Ord

namespace RuleRunnerDescr

def ofBuilder : RuleBuilder → RuleRunnerDescr
  | .identity => .identity
  | .applyHyps => .applyHyps
  | .ipureIntro => .ipureIntro
  | .imodintro => .imodIntro
  | .imod => .imod
  | .iexact => .iexact
  | _ => .custom

def ofInfo (info : RuleInfo) : RuleRunnerDescr :=
  ofBuilder info.builder

end RuleRunnerDescr

structure ChildGoalSpec where
  goal : MVarId
  irisGoal : Iris.ProofMode.IrisGoal
  mvars : Std.HashSet MVarId

structure RappSpec where
  rappState : NodeState
  obunState : NodeState
  obunKind : ObunKind
  childGoals : Array ChildGoalSpec
  fullContextIrisSubgoals : Array Iris.ProofMode.IrisGoal
  consumedSpatialHyp? : Option IrisHyp
  consumedLeanHyp? : Option FVarId := none
  finalizedSpatialSplits : Array (Array IrisHyp)
  metaState : SavedState
  introducedMVars : Std.HashSet MVarId := {}
  assignedMVars : Std.HashSet MVarId := {}
  parentState? : Option GoalState := none

structure RuleInput where
  parentRef : GoalRef
  parent : Goal
  matchResult : RuleMatch
  goal : MVarId
  state : SavedState
  managedObun? : Option ObunRef
  managedState? : Option SavedState

namespace RuleInput

def isManaged (input : RuleInput) : Bool :=
  input.managedObun?.isSome

def stateForManaged (input : RuleInput) : SavedState :=
  input.managedState?.getD input.state

end RuleInput

structure RuleEffect where
  rappSpec : RappSpec
  managedObunPostState? : Option SavedState := none

structure RuleOutput where
  ruleEffects : Array RuleEffect

namespace RuleOutput

instance : EmptyCollection RuleOutput where
  emptyCollection := { ruleEffects := #[] }

def single (rappSpec : RappSpec) : RuleOutput :=
  { ruleEffects := #[{ rappSpec }] }

def singleEffect (effect : RuleEffect) : RuleOutput :=
  { ruleEffects := #[effect] }

def ofRappSpecs (rappSpecs : Array RappSpec) : RuleOutput :=
  { ruleEffects := rappSpecs.map fun rappSpec => { rappSpec } }

end RuleOutput

abbrev RuleRunner (Q : Type) [Queue Q] :=
  RuleInput → SearchM Q RuleOutput

end Iris.ProofMode.Aesop
