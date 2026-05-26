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

/- Auxiliary effects produced by a rule application. -/
inductive RuleEffect where
  | multipleGoals (fullContextIrisSubgoals: Array IrisGoal)
    (usedHyp? : Option AppliedHyp)
  | contextManagement (fullContextIrisSubgoals : Array IrisGoal)
    (usedHyp? : Option AppliedHyp)
  | closeGoal (usedHyp? : Option AppliedHyp)

namespace RuleEffect

def fullContextIrisSubgoals : RuleEffect → Array IrisGoal
  | contextManagement irisSubgoals ..  => irisSubgoals
  | _ => #[]

def usedHyp? : RuleEffect → Option AppliedHyp
  | multipleGoals _ hyp => hyp
  | contextManagement _ hyp => hyp
  | closeGoal hyp => hyp

def consumedSpatialHyp? : RuleEffect → Option IrisHyp
  | multipleGoals _ usedHyp? => usedHyp?.bind AppliedHyp.consumedSpatialHyp?
  | contextManagement _ usedHyp? => usedHyp?.bind AppliedHyp.consumedSpatialHyp?
  | closeGoal usedHyp? => usedHyp?.bind AppliedHyp.consumedSpatialHyp?

end RuleEffect

/- Rule application nodes' specification -/
structure RappSpec where
  goals : Array SubGoal
  postState : SavedState
  successPossibility : Percent
  effect : Option RuleEffect
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
  ofRappSpec { goals, postState, successPossibility, effect := some effect }

end RuleOutput

abbrev RuleRunner (Q : Type) [Queue Q] :=
  RuleInput → SearchM Q RuleOutput

abbrev RuleReplayer :=
  RuleReplayInput → ProofModeM (Array MVarId)

end Iris.ProofMode.Aesop
