module

public meta import Iris.ProofMode.Aesop.Rule.Commit.Basic
public meta import Iris.ProofMode.Tactics.Cases

public meta section

namespace Iris.ProofMode.Aesop.Rule.ICases

open Lean Meta Qq Std
open Iris.BI
open Iris.ProofMode

variable {Q : Type} [Queue Q]

private structure ICasesExpansion where
  usedHyp : AppliedHyp
  goals : Array SubGoal
  fullContextIrisSubgoals : Array IrisGoal
  postState : SavedState

private def mkHypExpansion?
    {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)}
    (irisGoal : IrisGoal) (tag : Name)
    (name : Name) (ivar : IVarId) (p : Q(Bool)) (hypType : Q($prop)) :
    MetaM (Option ICasesExpansion) := do
  let left ← mkFreshExprMVarQ prop
  let right ← mkFreshExprMVarQ prop
  let .some _ ← trySynthInstanceProbeQ q(IntoOr $hypType $left $right)
    | return none

  /- Mirror ISplit.mkAndChildren: each branch records the full IrisGoal after splitting the consumed hypothesis. -/
  let some ⟨_, _, remainingHyps, out, removedHypType, removedP, _, _⟩ ←
      irisGoal.hyps.removeG false λ _ ivar' _ _ => do
        if ivar == ivar' then return some ()
        else return none
    | throwError "iaesop: icases candidate disappeared from Hyps"
  have : $out =Q iprop(□?$removedP $removedHypType) := ⟨⟩
  let leftIvar ← mkFreshIVarId
  let leftHyps := Hyps.add irisGoal.bi name leftIvar removedP left remainingHyps
  let rightIvar ← mkFreshIVarId
  let rightHyps := Hyps.add irisGoal.bi name rightIvar removedP right remainingHyps
  let leftIrisGoal := { irisGoal with e := _, hyps := leftHyps }
  let leftExpr ← mkFreshExprSyntheticOpaqueMVar (IrisGoal.toExpr leftIrisGoal) tag
  let leftGoal := { goal := leftExpr.mvarId!, addedFVars := {}, removedFVars := {} }
  let rightIrisGoal := { irisGoal with e := _, hyps := rightHyps }
  let rightExpr ← mkFreshExprSyntheticOpaqueMVar (IrisGoal.toExpr rightIrisGoal) tag
  let rightGoal := { goal := rightExpr.mvarId!, addedFVars := {}, removedFVars := {} }
  return some {
    usedHyp := if isTrue p then .intuitionistic { name, ivar } else .spatial { name, ivar }
    goals := #[leftGoal, rightGoal]
    fullContextIrisSubgoals := #[leftIrisGoal, rightIrisGoal]
    postState := ← saveState
  }

private partial def collectFromIris
    {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)}
    (irisGoal : IrisGoal) (tag : Name) (baseState : SavedState) :
    ∀ {e}, Hyps bi e → MetaM (Array ICasesExpansion)
  | _, .emp _ => return #[]
  | _, .sep _ _ _ _ lhs rhs => do
    let lhsExpansions ← collectFromIris irisGoal tag baseState lhs
    let rhsExpansions ← collectFromIris irisGoal tag baseState rhs
    return lhsExpansions ++ rhsExpansions
  | _, .hyp _ name ivar p ty _ => do
    baseState.restore
    let expansion? ← mkHypExpansion? (bi := bi) irisGoal tag name ivar p ty
    baseState.restore
    return expansion?.toArray

def run (input : RuleInput) : SearchM Q RuleOutput := do
  let goal := input.goal
  let expansions ← liftM do
    restoreState input.state
    goal.withContext do
      let goalType ← instantiateMVars (← goal.getType)
      let some irisGoal := parseIrisGoal? goalType
        | throwError "iaesop: icases rule search must work in iris proof-mode context"
      collectFromIris irisGoal (← goal.getTag) (← saveState) irisGoal.hyps
  if expansions.isEmpty then
    return {}
  let specs ← expansions.mapM λ expansion => do
    return {
      goals := expansion.goals
      postState := expansion.postState
      successPossibility := .hundred
      effect := some (.multipleGoals
        expansion.fullContextIrisSubgoals (some expansion.usedHyp))
    }
  return RuleOutput.ofRappSpecs specs

def replay (input : RuleReplayInput) : ProofModeM (Array MVarId) := do
  let some usedHyp := input.rapp.usedHyp?
    | throwError "iaesop(baseline): icases replay is missing the selected hypothesis"
  input.goal.withContext do
    let goalType ← instantiateMVars (← input.goal.getType)
    let some { prop, bi, hyps, goal := target, .. } := parseIrisGoal? goalType
      | throwError "iaesop(baseline): icases replay expected an Iris goal"
    let some ⟨_, _, remainingHyps, out, hypType, p, _, removePf⟩ ←
        hyps.removeG false λ name _ p _ => do
          match usedHyp with
          | .spatial hyp =>
            if hyp.name == name && !isTrue p then return some () else return none
          | .intuitionistic hyp =>
            if hyp.name == name && isTrue p then return some () else return none
          | .lean .. => return none
      | throwError "iaesop(baseline): icases replay selected hypothesis disappeared"
    have : $out =Q iprop(□?$p $hypType) := ⟨⟩
    let left ← mkFreshExprMVarQ prop
    let right ← mkFreshExprMVarQ prop
    let some inst ← ProofModeM.trySynthInstanceQ q(IntoOr $hypType $left $right)
      | throwError "iaesop(baseline): icases replay could not view the hypothesis as a disjunction"
    let _ : Q(IntoOr $hypType $left $right) := inst
    let usedName :=
      match usedHyp with
      | .spatial hyp | .intuitionistic hyp => hyp.name
      | .lean .. => `H
    let leftIvar ← mkFreshIVarId
    let leftHyps := Hyps.add bi usedName leftIvar p left remainingHyps
    let rightIvar ← mkFreshIVarId
    let rightHyps := Hyps.add bi usedName rightIvar p right remainingHyps
    let tag ← input.goal.getTag
    let leftProof ← mkBIGoal leftHyps target tag
    let rightProof ← mkBIGoal rightHyps target tag
    input.goal.assign q(($removePf).1.trans (or_elim' $leftProof $rightProof))
    return #[leftProof.mvarId!, rightProof.mvarId!]

end Iris.ProofMode.Aesop.Rule.ICases
