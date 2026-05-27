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
  | icases
  | ipureIntro
  | iExist
  | imodIntro
  | imod
  | isplit
  | custom
  deriving Inhabited, BEq, Hashable, Ord

namespace RuleRunnerDescr

def ofBuilder : RuleBuilder → RuleRunnerDescr
  | .identity => .identity
  | .applyHyps => .applyHyps
  | .icases => .icases
  | .ipureIntro => .ipureIntro
  | .iExist => .iExist
  | .imodintro => .imodIntro
  | .imod => .imod
  | .isplit => .isplit
  | _ => .custom

def ofInfo (info : RuleInfo) : RuleRunnerDescr :=
  ofBuilder info.builder

end RuleRunnerDescr

structure RuleInput where
  goal : MVarId
  depth : Nat
  /- all involved meta variables in goal -/
  mvars : Array MVarId
  state : SavedState
  matchResult : RuleMatch

structure RuleReplayInput where
  goal : MVarId
  rapp : Rapp

/- SubGoal produced by a rule application -/
structure SubGoal where
  goal : MVarId
  addedFVars : Std.HashSet FVarId
  removedFVars : Std.HashSet FVarId
  deriving Inhabited

/- Concrete effects produced by a rule application -/
inductive RuleAction where
  | splitGoals (subGoals : Array IrisGoal)
  | manageContext (templates : Array IrisGoal)
  | closeGoal
  deriving Inhabited

/- Information produced by a rule application -/
structure RuleEffect where
  generatedSpatialHyp? : Option IrisHyp := none
  usedHyp? : Option AppliedHyp := none
  action : Option RuleAction := none
  deriving Inhabited

namespace RuleEffect

def consumedSpatialHyp? (effect : RuleEffect) : Option IrisHyp :=
  match effect.usedHyp? with
  | none => none
  | some usedHyp => usedHyp.consumedSpatialHyp?

end RuleEffect

/- Rule application nodes' specification -/
structure RappSpec where
  goals : Array SubGoal
  postState : SavedState
  successPossibility : Percent
  effect : RuleEffect
  -- [TODO] Add script here

structure RuleOutput where
  rappSepcs : Array RappSpec
  deriving Inhabited

namespace RuleOutput

instance : EmptyCollection RuleOutput where
  emptyCollection := { rappSepcs := #[] }

def ofRappSpec (rappSpec : RappSpec) : RuleOutput :=
  { rappSepcs := #[rappSpec] }

def ofRappSpecs (rappSpecs : Array RappSpec) : RuleOutput :=
  { rappSepcs := rappSpecs }

def ofEffect (postState : SavedState) (effect : RuleEffect)
    (goals : Array SubGoal := #[])
    (successPossibility : Percent := Percent.hundred) : RuleOutput :=
  ofRappSpec { goals, postState, successPossibility, effect := effect }

end RuleOutput

abbrev RuleRunner (Q : Type) [Queue Q] :=
  RuleInput → SearchM Q RuleOutput

abbrev RuleReplayer :=
  RuleReplayInput → ProofModeM (Array MVarId)

end Iris.ProofMode.Aesop
