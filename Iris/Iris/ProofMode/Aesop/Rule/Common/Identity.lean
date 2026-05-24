module

public meta import Iris.ProofMode.Aesop.Rule.Commit.Basic
public meta import Iris.ProofMode.Tactics.Split

public meta section

namespace Iris.ProofMode.Aesop.Rule.Identity

open Lean Meta Qq Std

variable {Q : Type} [Queue Q]

private def mkSplitChildren (goal : MVarId) :
    MetaM (Option (Array SubGoal × Array IrisGoal)) := do
  goal.withContext do
    let goalType ← instantiateMVars (← goal.getType)
    let some irisGoal := parseIrisGoal? goalType
      | throwError "iaesop: internal error: identity must work in iris proof-mode context"
    let { prop, goal := target, .. } := irisGoal
    let target : Q($prop) ← instantiateMVars target
    let lhs : Q($prop) ← mkFreshExprMVarQ prop
    let rhs : Q($prop) ← mkFreshExprMVarQ prop
    match ← ProofMode.trySynthInstanceQ q(FromSep $target $lhs $rhs) with
    | .none | .undef => return none
    | .some _ =>
      let lhs : Q($prop) ← instantiateMVars lhs
      let rhs : Q($prop) ← instantiateMVars rhs
      let targets := #[lhs, rhs]
      let mut children : Array SubGoal := #[]
      let mut fullContextIrisSubgoals : Array IrisGoal := #[]
      for target in targets do
        let irisGoal := { irisGoal with goal := target }
        let goalExpr ← mkFreshExprSyntheticOpaqueMVar (IrisGoal.toExpr irisGoal) (← goal.getTag)
        let goal := goalExpr.mvarId!
        children := children.push { goal, addedFVars := {}, removedFVars := {} }
        fullContextIrisSubgoals := fullContextIrisSubgoals.push irisGoal
      return some (children, fullContextIrisSubgoals)

def run (input : RuleInput) : SearchM Q RuleOutput := do
  let goal := input.goal
  let (some (children, fullContextIrisSubgoals), postState) ← liftM do
      restoreState input.state
      let children? ← mkSplitChildren goal
      let postState ← saveState
      return (children?, postState)
    | return {}

  dbg_trace s!"identity split target into {children.size} goals"
  for irisGoal in fullContextIrisSubgoals do
    let targetFmt ← liftM <| ppExpr irisGoal.goal
    dbg_trace s!"  identity child target: {targetFmt.pretty}"

  return RuleOutput.ofRappSpec {
    goals := children
    postState := postState
    successPossibility := .hundred
    effect := some (.contextManagement fullContextIrisSubgoals none)
  }

/- Replay one identity split and return the immediate left and right subgoals. -/
private def replaySplit (goalMVarId : MVarId)
    (contexts : Array (Array IrisHyp)) : ProofModeM (Array MVarId) := do
  if contexts.size != 2 then
    throwError s!"iaesop(baseline): identity replay expected two split contexts, got {contexts.size}"
  let some _ := contexts[0]?
    | throwError "iaesop(baseline): identity replay is missing the left split context"
  let some rhsContext := contexts[1]?
    | throwError "iaesop(baseline): identity replay is missing the right split context"
  goalMVarId.withContext do
    let goalType ← instantiateMVars (← goalMVarId.getType)
    let some { prop, bi, hyps, goal := target, .. } := parseIrisGoal? goalType
      | throwError "iaesop(baseline): identity replay expected an Iris goal"
    let Q1 ← mkFreshExprMVarQ prop
    let Q2 ← mkFreshExprMVarQ prop
    let some _ ← ProofModeM.trySynthInstanceQ q(FromSep $target $Q1 $Q2)
      | throwError "iaesop(baseline): identity replay cannot split target"
    let rightNames := rhsContext.map (·.name)
    let ⟨_, _, lhsHyps, rhsHyps, pf⟩ :=
      hyps.split bi λ name _ => rightNames.contains name
    let lhsGoal ← mkBIGoal lhsHyps Q1 (← goalMVarId.getTag)
    let rhsGoal ← mkBIGoal rhsHyps Q2 (← goalMVarId.getTag)
    goalMVarId.assign q(sep_split (Q := $target) $pf $lhsGoal $rhsGoal)
    return #[lhsGoal.mvarId!, rhsGoal.mvarId!]

/- [Note] Make sure you are in the correct context -/
def replay (input : RuleReplayInput) : ProofModeM (Array MVarId) := do
  let rapp := input.rapp

  /- Sanity check -/
  let obun ← rapp.children.get
  if !obun.state.isProven then
    throwError s!"iaesop(baseline): identity replay expected child obun to be proven"
  if !obun.kind.isManaged || obun.finalizedSpatialSplits.size <= 1 then
    throwError s!"iaesop(baseline): identity replay expected a managed obun"
  if obun.finalizedSpatialSplits.isEmpty then
    throwError s!"iaesop(baseline): identity replay has no finalized spatial splits"
  if obun.finalizedSpatialSplits.size != obun.goals.size then
    throwError s!"iaesop(baseline): identity replay got " ++
      s!"{obun.finalizedSpatialSplits.size} finalized split entries for {obun.goals.size} child goals"

  /- Assign the proof term and return all replay-generated child metavariables. -/
  let goals ← replaySplit input.goal obun.finalizedSpatialSplits
  if goals.size != obun.goals.size then
    throwError s!"iaesop(baseline): identity replay produced {goals.size} goals for {obun.goals.size} search children"
  return goals

end Iris.ProofMode.Aesop.Rule.Identity
