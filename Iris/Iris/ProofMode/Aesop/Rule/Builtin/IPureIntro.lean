module

public meta import Lean.Meta.Tactic.Simp.SimpAll
public meta import Iris.ProofMode.Aesop.Rule.Common
public meta import Iris.ProofMode.Tactics.Pure

public meta section

namespace Iris.ProofMode.Aesop.Rule.Builtin.IPureIntro

open Lean Meta Qq Std
open Iris.BI
open Iris.ProofMode
open Iris.ProofMode.Aesop

variable {Q : Type} [Queue Q]

private def tryCloseByLocalAssumption (goal : MVarId) : MetaM Bool := do
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    let preState ← saveState
    for ldecl in ← getLCtx do
      if ldecl.isImplementationDetail then
        continue
      restoreState preState
      let hypType ← instantiateMVars ldecl.type
      if ← isDefEq hypType target then
        goal.assign (mkFVar ldecl.fvarId)
        return true
    restoreState preState
    let ctx ← Simp.mkContext
      (config := ({} : Simp.Config))
      (simpTheorems := #[← getSimpTheorems])
      (congrTheorems := ← getSimpCongrTheorems)
    let ctx := ctx.setFailIfUnchanged false
    let (result?, _) ←
      Meta.simpGoal goal ctx (simprocs := #[]) (discharge? := none)
        (simplifyTarget := true) (fvarIdsToSimp := #[])
    match result? with
    | none => return true
    | some _ =>
      restoreState preState
      return false

def run (input : RuleInput) : SearchM Q RuleOutput := do
  let goal := input.goal
  let state := input.state
  let result? ← liftM (show ProofModeM (Option SavedState) from do
    liftM <| state.restore
    let prePMState ← getThe ProofModeM.State
    try
      goal.withContext do
        let goalType ← instantiateMVars (← goal.getType)
        let some { e, goal := target, .. } := parseIrisGoal? goalType
          | return none
        let b : Q(Bool) ← mkFreshExprMVarQ q(Bool)
        let φ : Q(Prop) ← mkFreshExprMVarQ q(Prop)
        let .some h ← ProofModeM.trySynthInstanceQ
            q(FromPure $b $target .out $φ)
          | return none
        let m : Q($φ) ← mkFreshExprMVar (← instantiateMVars φ)
        unless ← tryCloseByLocalAssumption m.mvarId! do
          addMVarGoal m.mvarId!
        match ← whnf b with
        | .const ``true _ =>
          have : $b =Q true := ⟨⟩
          let .some _ ← trySynthInstanceQ q(Affine $e)
            | throwError "ipure_intro: context is not affine"
          goal.assign q(pure_intro_affine (P := $e) (Q := $target) $h $m)
        | .const ``false _ =>
          have : $b =Q false := ⟨⟩
          goal.assign q(pure_intro_spatial (P := $e) (Q := $target) $h $m)
        | _ =>
          throwError
            "ipure_intro: bug in typeclass instances, cannot reduce {b} to true or false"
        return some (← liftM (show MetaM SavedState from saveState))
    catch _ =>
      set prePMState
      liftM <| state.restore
      return none)
  let some postState := result?
    | return {}
  return RuleOutput.single {
    rappState := .proven
    obunState := .proven
    obunKind := .plain
    childGoals := #[]
    fullContextIrisSubgoals := #[]
    consumedSpatialHyp? := none
    finalizedSpatialSplits := #[]
    metaState := postState
    parentState? := some (.provenByRuleApplication #[])
  }

end Iris.ProofMode.Aesop.Rule.Builtin.IPureIntro
