module

public meta import Iris.ProofMode.Aesop.Rule.Commit.Basic

public meta section

namespace Iris.ProofMode.Aesop.Rule.Identity

open Lean Meta Qq Std
open Iris.BI
open Iris.ProofMode

variable {Q : Type} [Queue Q]

/- Auxiliary function for split multiple goals -/
private partial def splitSepTargets
    {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)}
    (target : Q($prop)) : MetaM (Array Q($prop)) := do
  let target : Q($prop) ← instantiateMVars target
  let lhs : Q($prop) ← mkFreshExprMVarQ prop
  let rhs : Q($prop) ← mkFreshExprMVarQ prop
  match ← ProofMode.trySynthInstanceQ q(FromSep $target $lhs $rhs) with
  | .some _ =>
    let lhs : Q($prop) ← instantiateMVars lhs
    let rhs : Q($prop) ← instantiateMVars rhs
    return (← splitSepTargets (prop := prop) (bi := bi) lhs) ++
      (← splitSepTargets (prop := prop) (bi := bi) rhs)
  | _ =>
    return #[target]

private def mkSplitChildren (goal : MVarId) :
    MetaM (Option (Array SubGoal × Array IrisGoal)) := do
  goal.withContext do
    let goalType ← instantiateMVars (← goal.getType)
    let some irisGoal := parseIrisGoal? goalType
      | throwError "iaesop: internal error: identity must work in iris proof-mode context"
    let targets ← splitSepTargets (prop := irisGoal.prop) (bi := irisGoal.bi)
      (← instantiateMVars irisGoal.goal)
    -- [TODO] Should I report error here if we have index match ?
    if targets.size <= 1 then return none
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

def replay (input : RuleReplayInput) : SearchM Q MVarId := do
  return input.goal

end Iris.ProofMode.Aesop.Rule.Identity
