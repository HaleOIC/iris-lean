module

public meta import Iris.ProofMode.Aesop.Rule.Commit.Basic
public meta import Iris.ProofMode.Tactics.LeftRight

public meta section

namespace Iris.ProofMode.Aesop.Rule.ILeftRight

open Lean Meta Qq Std
open Iris.BI
open Iris.ProofMode

variable {Q : Type} [Queue Q]

inductive Side where
  | left
  | right
  deriving Repr

instance : ToString Side where
  toString
    | .left => "ileft"
    | .right => "iright"

/- Run search according to the given side -/
private def runSide (side : Side) (input : RuleInput) : SearchM Q RuleOutput := do
  let some (child, postState) ← liftM (show ProofModeM (Option (SubGoal × SavedState)) from do
      input.state.restore
      input.goal.withContext do
        let goalType ← instantiateMVars (← input.goal.getType)
        let some irisGoal := parseIrisGoal? goalType
          | throwError "iaesop: ileft/iright rule search must work in iris proof-mode"
        let baseState ← liftM (m := MetaM) saveState
        let { prop, hyps, goal := target, .. } := irisGoal
        let lhs ← mkFreshExprMVarQ prop
        let rhs ← mkFreshExprMVarQ prop
        match ← trySynthInstanceProbeQ q(FromOr $target $lhs $rhs) with
        | .none | .undef => baseState.restore; return none
        | .some _ =>
          let newTarget := match side with | .left => lhs |.right => rhs
          let childExpr ← mkBIGoal hyps newTarget (← input.goal.getTag)
          return some ({ goal := childExpr.mvarId!, addedFVars := {}, removedFVars := {} },
            ← liftM (m := MetaM) saveState)
    )
    | return {}
  return RuleOutput.ofRappSpec {
    goals := #[child]
    postState
    successPossibility := .hundred
    effect := default
  }

/- [Note] Make sure you are in the correct context -/
private def replaySide (side : Side) (input : RuleReplayInput) : ProofModeM (Array MVarId) := do
  input.goal.withContext do
    let goalType ← instantiateMVars (← input.goal.getType)
    let some { prop, e, hyps, goal := target, .. } := parseIrisGoal? goalType
      | throwError s!"iaesop(baseline): {side} replay expected an Iris goal"
    have e : Q($prop) := e
    let lhs ← mkFreshExprMVarQ prop
    let rhs ← mkFreshExprMVarQ prop
    let some inst ← ProofModeM.trySynthInstanceQ q(FromOr $target $lhs $rhs)
      | throwError s!"iaesop(baseline): {side} replay could not view the target as a disjunction"
    let lhs : Q($prop) ← instantiateMVars lhs
    let rhs : Q($prop) ← instantiateMVars rhs
    let inst : Q(FromOr $target $lhs $rhs) ← instantiateMVars inst
    match side with
    | .left =>
      let childProof : Q($e ⊢ $lhs) ← mkBIGoal hyps lhs (← input.goal.getTag)
      input.goal.assign q(from_or_l (Q := $target) (A1 := $lhs) (A2 := $rhs) (inst := $inst) $childProof)
      return #[childProof.mvarId!]
    | .right =>
      let childProof : Q($e ⊢ $rhs) ← mkBIGoal hyps rhs (← input.goal.getTag)
      input.goal.assign q(from_or_r (Q := $target) (A1 := $lhs) (A2 := $rhs) (inst := $inst) $childProof)
      return #[childProof.mvarId!]

def runLeft (input : RuleInput) : SearchM Q RuleOutput :=
  runSide .left input

def runRight (input : RuleInput) : SearchM Q RuleOutput :=
  runSide .right input

def replayLeft (input : RuleReplayInput) : ProofModeM (Array MVarId) :=
  replaySide .left input

def replayRight (input : RuleReplayInput) : ProofModeM (Array MVarId) :=
  replaySide .right input

end Iris.ProofMode.Aesop.Rule.ILeftRight
