module

public meta import Iris.ProofMode.Aesop.Rule.Commit.Basic
public meta import Iris.ProofMode.Tactics.Pure

public meta section

namespace Iris.ProofMode.Aesop.Rule.IPureIntro

open Lean Meta Qq Std
open Iris.BI
open Iris.ProofMode

variable {Q : Type} [Queue Q]

/- [Note] Only try to solve lean hypothesis after `pure_intro` using assumption or simp -/
private def tryCloseByLocalAssumptionOrSimp (goal : MVarId) : MetaM Bool := do
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    let preState ← saveState
    for ldecl in ← getLCtx do
      if ldecl.isImplementationDetail then
        continue
      preState.restore
      let hypType ← instantiateMVars ldecl.type
      if ← isDefEq hypType target then
        goal.assign (mkFVar ldecl.fvarId)
        return true
    preState.restore
    let ctx ← Simp.mkContext {} #[← getSimpTheorems] (← getSimpCongrTheorems)
    let ctx := ctx.setFailIfUnchanged false
    let (result?, _) ←
      Meta.simpGoal goal ctx (simprocs := #[]) (discharge? := none)
        (simplifyTarget := true) (fvarIdsToSimp := #[])
    match result? with
    | none => return true
    | some _ =>
      restoreState preState
      return false

/- Keep enough failure detail for replay diagnostics while letting search treat every
unsuccessful probe as "this rule does not apply here". -/
private inductive PureIntroResult where
  | success (postState : SavedState)
  | notIrisGoal
  | notPure
  | pureGoalUnproved
  | nonAffineContext
  | stuckPurityFlag

/- Shared implementation for search and replay: synthesize `FromPure`, solve the
extracted Lean proposition locally, then assign the proof-mode goal. -/
private def tryAssignPureIntro (goal : MVarId) : MetaM PureIntroResult := do
  goal.withContext do
    let goalType ← instantiateMVars (← goal.getType)
    let some { e, goal := target, .. } := parseIrisGoal? goalType
      | return .notIrisGoal
    let b : Q(Bool) ← mkFreshExprMVarQ q(Bool)
    let φ : Q(Prop) ← mkFreshExprMVarQ q(Prop)
    let .some (h, _) ← ProofMode.trySynthInstanceQ q(FromPure $b $target .out $φ)
      | return .notPure
    let proof : Q($φ) ← mkFreshExprMVar (← instantiateMVars φ)
    unless ← tryCloseByLocalAssumptionOrSimp proof.mvarId! do
      return .pureGoalUnproved
    let h : Q(FromPure $b $target .out $φ) := h
    match ← whnf b with
    | .const ``true _ =>
      have : $b =Q true := ⟨⟩
      let .some _ ← trySynthInstanceQ q(Affine $e)
        | return .nonAffineContext
      goal.assign q(pure_intro_affine (P := $e) (Q := $target) $h $proof)
    | .const ``false _ =>
      have : $b =Q false := ⟨⟩
      goal.assign q(pure_intro_spatial (P := $e) (Q := $target) $h $proof)
    | _ =>
      return .stuckPurityFlag
    return .success (← saveState)

/- Search for the possibility of `ipure_intro` applications -/
def run (input : RuleInput) : SearchM Q RuleOutput := do
  let goal := input.goal
  let .success postState ← liftM (show MetaM PureIntroResult from do
    input.state.restore
    tryAssignPureIntro goal)
    -- During search, a failed pure-intro attempt simply means "try another rule".
    | return {}
  return RuleOutput.ofEffect postState (.closeGoal none)

/- [Note] Make sure you are in the correct context -/
def replay (input : RuleReplayInput) : ProofModeM (Array MVarId) := do
  match ← liftM (m := MetaM) (tryAssignPureIntro input.goal) with
  | .success _ => return #[]
  | .notIrisGoal =>
    throwError "iaesop(baseline): ipureIntro replay expected an Iris goal"
  | .notPure =>
    throwError "iaesop(baseline): ipureIntro replay could not view the target as pure"
  | .pureGoalUnproved =>
    throwError "iaesop(baseline): ipureIntro replay could not prove the extracted pure goal"
  | .nonAffineContext =>
    throwError "iaesop(baseline): ipureIntro replay cannot discard the spatial context"
  | .stuckPurityFlag =>
    throwError "iaesop(baseline): ipureIntro replay got a stuck purity flag"

end Iris.ProofMode.Aesop.Rule.IPureIntro
