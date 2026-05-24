module

public meta import Lean.Meta.Tactic.Simp.SimpAll
public meta import Iris.ProofMode.Aesop.Rule.Commit.Basic
public meta import Iris.ProofMode.Tactics.Pure

public meta section

namespace Iris.ProofMode.Aesop.Rule.IPureIntro

open Lean Meta Qq Std
open Iris.BI
open Iris.ProofMode

variable {Q : Type} [Queue Q]

private def tryCloseByLocalAssumptionOrSimp (goal : MVarId) : MetaM Bool := do
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
  let some postState ← liftM (show MetaM (Option SavedState) from do
    restoreState input.state
    goal.withContext do
      let goalType ← instantiateMVars (← goal.getType)
      let some { e, goal := target, .. } := parseIrisGoal? goalType
        | return none
      let b : Q(Bool) ← mkFreshExprMVarQ q(Bool)
      let φ : Q(Prop) ← mkFreshExprMVarQ q(Prop)
      let .some (h, _) ← ProofMode.trySynthInstanceQ
          q(FromPure $b $target .out $φ)
        | return none
      let proof : Q($φ) ← mkFreshExprMVar (← instantiateMVars φ)
      unless ← tryCloseByLocalAssumptionOrSimp proof.mvarId! do
        return none
      let h : Q(FromPure $b $target .out $φ) := h
      match ← whnf b with
      | .const ``true _ =>
        have : $b =Q true := ⟨⟩
        let .some _ ← trySynthInstanceQ q(Affine $e)
          | return none
        goal.assign q(pure_intro_affine (P := $e) (Q := $target) $h $proof)
      | .const ``false _ =>
        have : $b =Q false := ⟨⟩
        goal.assign q(pure_intro_spatial (P := $e) (Q := $target) $h $proof)
      | _ =>
        return none
      return some (← saveState))
    | return {}
  return RuleOutput.ofEffect postState (.closeGoal none)

def replay (input : RuleReplayInput) : ProofModeM (Array MVarId) := do
  return #[input.goal]

end Iris.ProofMode.Aesop.Rule.IPureIntro
