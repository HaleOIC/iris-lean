module

public meta import Iris.ProofMode.Aesop.Rule.Common
public meta import Iris.ProofMode.Tactics.Cases

public meta section

namespace Iris.ProofMode.Aesop.Rule.IMod

open Lean Meta Qq Std
open Iris.BI
open Iris.ProofMode
open Iris.ProofMode.Aesop

variable {Q : Type} [Queue Q]

private structure ModHyp where
  name : Name
  ivar : IVarId

private partial def collectModHyps {u prop bi} :
    ∀ {e}, @Hyps u prop bi e → Array ModHyp
  | _, .emp _ => #[]
  | _, .hyp _ name ivar _ _ _ =>
    #[{ name, ivar }]
  | _, .sep _ _ _ _ lhs rhs =>
    collectModHyps lhs ++ collectModHyps rhs

private def hypBinder (name : Name) : ProofModeM (TSyntax ``binderIdent) := do
  let ident := mkIdent name.eraseMacroScopes
  `(binderIdent| $ident:ident)

private def runOnHyp (goal : MVarId) (hyp : ModHyp) :
    ProofModeM (Option (ChildGoalSpec × SavedState)) := do
  let preState ← liftM (show MetaM SavedState from saveState)
  let prePMState ← getThe ProofModeM.State
  try
    goal.withContext do
      let goalType ← instantiateMVars (← goal.getType)
      let some irisGoal := parseIrisGoal? goalType
        | return none
      let some ⟨_, _, hyps', out, ty, p, _, removePf⟩ ←
          irisGoal.hyps.removeG true fun _ ivar _ _ => do
            if ivar == hyp.ivar then return some ()
            else return none
        | return none
      have : $out =Q iprop(□?$p $ty) := ⟨⟩
      let childRef ← IO.mkRef (none : Option MVarId)
      let pat := iCasesPat.mod (.one (← hypBinder hyp.name))
      let proof ←
        iCasesCore irisGoal.bi hyps' irisGoal.goal pat p ty
          fun hyps goal' => do
            let childExpr ← mkBIGoal hyps goal' (← goal.getTag)
            childRef.set (some childExpr.mvarId!)
            return childExpr
      let some childGoal := ← childRef.get
        | throwError "iaesop: internal error: imod did not generate a goal"
      goal.assign q(($removePf).1.trans $proof)
      let child ← liftM <| mkChildGoalSpec childGoal
      return some (child, ← liftM (show MetaM SavedState from saveState))
  catch _ =>
    set prePMState
    liftM <| preState.restore
    return none

def run (parentRef : GoalRef) (_matchResult : RuleMatch) :
    SearchM Q (Array RappSpec) := do
  let parent ← parentRef.get
  let (goal, state) ← normalizedGoalAndState "imod" parent
  let expansions ← liftM (show ProofModeM (Array (ChildGoalSpec × SavedState)) from do
    liftM <| state.restore
    goal.withContext do
      let goalType ← instantiateMVars (← goal.getType)
      let some { hyps, .. } := parseIrisGoal? goalType
        | return #[]
      let mut expansions := #[]
      for hyp in collectModHyps hyps do
        liftM <| state.restore
        if let some expansion ← runOnHyp goal hyp then
          expansions := expansions.push expansion
      return expansions)
  expansions.mapM λ (child, postState) => do
    return {
      rappState := .unknown
      obunState := .unknown
      obunKind := .plain
      childGoals := #[child]
      fullContextIrisSubgoals := #[child.irisGoal]
      consumedSpatialHyp? := none
      finalizedSpatialSplits := #[]
      metaState := postState
    }

end Iris.ProofMode.Aesop.Rule.IMod
