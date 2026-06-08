module

public meta import Iris.ProofMode.Aesop.Rule.Commit.Basic
public meta import Iris.ProofMode.Tactics.Pure

public meta section

namespace Iris.ProofMode.Aesop.Rule.IPureIntro

open Lean Elab Tactic Meta Qq
open Iris.BI
open Iris.ProofMode

variable {Q : Type} [Queue Q]

/- Run the configured tactic on the pure Lean goal. The tactic is accepted only
if it closes the focused goal without leaving further subgoals. -/
private def tryCloseByPureSolver (goal : MVarId) (solver : Syntax) : ProofModeM Bool := do
  let preState ← liftM (m := MetaM) saveState
  let prePMState ← getThe ProofModeM.State
  try
    let goals ← withSuppressedMessages <| evalTacticAt solver goal
    Term.synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := true)
    let closed ← goal.isAssignedOrDelayedAssigned
    let hasOpenGoal ← goals.anyM λ goal => do
      return !(← goal.isAssignedOrDelayedAssigned)
    if closed && !hasOpenGoal then
      return true
    set prePMState
    liftM (m := MetaM) preState.restore
    return false
  catch _ =>
    set prePMState
    liftM (m := MetaM) preState.restore
    return false

/- Keep enough failure detail for replay diagnostics while letting search treat every
unsuccessful probe as "this rule does not apply here". -/
private inductive PureIntroResult where
  | success (postState : Meta.SavedState)
  | notIrisGoal
  | notPure
  | pureGoalUnproved
  | nonAffineContext
  | stuckPurityFlag

/- Shared implementation for search and replay: synthesize `FromPure`, solve the
extracted Lean proposition locally, then assign the proof-mode goal. -/
private def tryAssignPureIntro (goal : MVarId)
    (pureSolver : Syntax) : ProofModeM PureIntroResult := do
  goal.withContext do
    let goalType ← instantiateMVars (← goal.getType)
    let some { e, goal := target, .. } := parseIrisGoal? goalType
      | return .notIrisGoal
    let b : Q(Bool) ← mkFreshExprMVarQ q(Bool)
    let φ : Q(Prop) ← mkFreshExprMVarQ q(Prop)
    let .some (h, _) ← trySynthInstanceProbeQ q(FromPure $b $target .out $φ)
      | return .notPure
    let proof : Q($φ) ← mkFreshExprMVar (← instantiateMVars φ)
    unless ← tryCloseByPureSolver proof.mvarId! pureSolver do
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
    return .success (← liftM (m := MetaM) saveState)

/- Search for the possibility of `ipureintro` applications -/
def run (input : RuleInput) : SearchM Q RuleOutput := do
  let goal := input.goal
  let pureSolver := (← readThe SearchM.Context).config.pureSolver
  let .success postState ← liftM (m := ProofModeM) do
    input.state.restore
    tryAssignPureIntro goal pureSolver
    -- During search, a failed pure-intro attempt simply means "try another rule".
    | return {}
  return RuleOutput.ofEffect postState { action := some .closeGoal }

/- [Note] Make sure you are in the correct context -/
def replay (input : RuleReplayInput) : ProofModeM (Array MVarId) := do
  match ← tryAssignPureIntro input.goal input.config.pureSolver with
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
