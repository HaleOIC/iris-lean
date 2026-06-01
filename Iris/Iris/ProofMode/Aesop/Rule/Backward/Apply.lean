module

public meta import Iris.ProofMode.Aesop.Rule.Backward.Shape
public meta import Iris.ProofMode.Aesop.Rule.Common.ApplyHyps

public meta section

namespace Iris.ProofMode.Aesop

open Lean Meta Qq Iris BI
open Iris.ProofMode

namespace Rule.Backward

private structure BackwardExpansion where
  goals : Array SubGoal
  fullContextIrisSubgoals : Array IrisGoal
  postState : SavedState

/-- Bridge a theorem proof into the current Iris BI as an intuitionistic proposition. -/
private def mkBackwardHyp? {prop : Q(Type u)} (bi : Q(BI $prop))
    (decl : Name) : MetaM (Option Q($prop)) := do
  let (_, body) ← instantiateTheorem decl
  if !(← Meta.isProp body) then
    return none
  have body : Q(Prop) := body
  let hyp ← mkFreshExprMVarQ prop
  match ← trySynthInstanceProbeQ q(AsEmpValid .into $body .in $prop .in $bi $hyp) with
  | .none | .undef => return none
  | .some _ =>
    let hyp : Q($prop) ← instantiateMVars hyp
    return some hyp

/-- Build a search expansion when a backward theorem directly proves the target. -/
private def mkCloseExpansion?
    {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)}
    (hyp target : Q($prop)) : MetaM (Option BackwardExpansion) := do
  let hyp : Q($prop) ← instantiateMVars hyp
  let target : Q($prop) ← instantiateMVars target
  let preState ← saveState
  match ← trySynthInstanceProbeQ q(FromAssumption true .in $hyp $target) with
  | .none | .undef => preState.restore; return none
  | .some _ =>
    let _ := ← instantiateMVars hyp
    let _ := ← instantiateMVars target
    return some {
      goals := #[],
      fullContextIrisSubgoals := #[],
      postState := ← saveState
    }

/-- Build a search expansion by applying a backward theorem to the current target. -/
private def mkExpansion? (decl : Name) (irisGoal : IrisGoal) (tag : Name)
    (baseState : SavedState) : MetaM (Option BackwardExpansion) := do
  let { bi, goal := target, .. } := irisGoal
  baseState.restore
  let some hyp ← mkBackwardHyp? bi decl
    | return none
  let bridgedState ← saveState
  if let some expansion ← mkCloseExpansion? (bi := bi) hyp target then
    return some expansion
  bridgedState.restore
  let some premises ← Rule.ApplyHyps.collectApplyPremises? (bi := bi) q(true) hyp target
    | baseState.restore; return none
  let (goals, fullContextIrisSubgoals) ←
    Rule.ApplyHyps.mkChildren irisGoal tag irisGoal.hyps premises
  return some {
    goals,
    fullContextIrisSubgoals,
    postState := ← saveState
  }

/-- Search stage work for a registered backward theorem. -/
def run {Q : Type} [Queue Q] (input : RuleInput) : SearchM Q RuleOutput := do
  let decl := input.matchResult.rule.id.name
  let expansion? ← liftM do
    restoreState input.state
    input.goal.withContext do
      let goalType ← instantiateMVars (← input.goal.getType)
      let some irisGoal := parseIrisGoal? goalType
        | throwError "iaesop: backward rule search must work in iris proof-mode context"
      mkExpansion? decl irisGoal (← input.goal.getTag) (← saveState)
  let some expansion := expansion?
    | return {}
  trace[iaesop.tactic] s!"backward selected {decl} and generated {expansion.goals.size} goals"
  for irisGoal in expansion.fullContextIrisSubgoals do
    let targetFmt ← liftM <| ppExpr irisGoal.goal
    trace[iaesop.tactic] s!"  backward child target: {targetFmt.pretty}"
  return RuleOutput.ofRappSpec {
    goals := expansion.goals
    postState := expansion.postState
    successPossibility := ⟨0.6⟩
    effect := {
      action :=
        if expansion.goals.isEmpty then some .closeGoal
        else if expansion.goals.size == 1 then none
        else some (.manageContext expansion.fullContextIrisSubgoals)
    }
  }

/-- Replay a registered backward theorem as an Iris intuitionistic proposition. -/
private def mkBackwardProof {prop : Q(Type u)} {bi : Q(BI $prop)} {e : Q($prop)}
    (decl : Name) : ProofModeM ((hyp : Q($prop)) × Q($e ⊢ $e ∗ □ $hyp)) := do
  let (value, body) ← instantiateTheorem decl
  if !(← Meta.isProp body) then
    throwError m!"iaesop(baseline): backward replay theorem {decl} is not a proposition"
  have body : Q(Prop) := body
  let hyp ← mkFreshExprMVarQ prop
  let some inst ← ProofModeM.trySynthInstanceQ q(AsEmpValid .into $body .in $prop .in $bi $hyp)
    | throwError m!"iaesop(baseline): backward replay cannot bridge theorem {decl} into Iris"
  let hyp : Q($prop) ← instantiateMVars hyp
  let body : Q(Prop) ← instantiateMVars body
  let value : Q($body) ← instantiateMVars value
  let inst : Q(AsEmpValid .into $body .in $prop .in $bi $hyp) := inst
  return ⟨hyp, q(have_asEmpValid (P := $hyp) (Q := $e) (h1 := $inst) $value)⟩

/-- Replay a close-goal backward theorem application. -/
private def replayClose (decl : Name) (goalMVarId : MVarId) :
    ProofModeM (Array MVarId) := do
  goalMVarId.withContext do
    let goalType ← instantiateMVars (← goalMVarId.getType)
    let some { bi, e, goal := target, .. } := parseIrisGoal? goalType
      | throwError "iaesop(baseline): backward replay expected an Iris goal"
    let ⟨hyp, haveProof⟩ ← mkBackwardProof (bi := bi) (e := e) decl
    let coreProof ← Rule.ApplyHyps.mkCloseCoreProof (bi := bi) (e := e) q(true) hyp target
    goalMVarId.assign q(Entails.trans $haveProof $coreProof)
    return #[]

/-- Replay a backward theorem application that generated premise subgoals. -/
private def replayApply (decl : Name) (goalMVarId : MVarId)
    (contexts : Array (Array IrisHyp)) : ProofModeM (Array MVarId) := do
  goalMVarId.withContext do
    let goalType ← instantiateMVars (← goalMVarId.getType)
    let some { bi, e, hyps, goal := target, .. } := parseIrisGoal? goalType
      | throwError "iaesop(baseline): backward replay expected an Iris goal"
    let ⟨hyp, haveProof⟩ ← mkBackwardProof (bi := bi) (e := e) decl
    let (coreProof, goals) ←
      Rule.ApplyHyps.replayApplyCore (bi := bi) hyps q(true) hyp target contexts (← goalMVarId.getTag)
    goalMVarId.assign q(Entails.trans $haveProof $coreProof)
    return goals

/-- Replay stage work for a registered backward theorem. -/
def replay (input : RuleReplayInput) : ProofModeM (Array MVarId) := do
  let decl := input.rapp.appliedRule.id.name
  let obun ← input.rapp.children.get
  if obun.goals.isEmpty || obun.kind.isInherited then
    replayClose decl input.goal
  else if obun.goals.size == 1 then
    if !obun.finalizedSpatialSplits.isEmpty then
      throwError "iaesop(baseline): backward replay found finalized spatial splits for a single-premise apply; expected no split information"
    replayApply decl input.goal #[]
  else
    if obun.finalizedSpatialSplits.size != obun.goals.size then
      throwError s!"iaesop(baseline): backward replay found {obun.finalizedSpatialSplits.size} finalized spatial splits for {obun.goals.size} generated goals"
    replayApply decl input.goal obun.finalizedSpatialSplits

end Rule.Backward

end Iris.ProofMode.Aesop
