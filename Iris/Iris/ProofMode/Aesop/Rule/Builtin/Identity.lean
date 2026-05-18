module

/-
Temporarily disabled: use `Rule.Common.Identity` while common is the only
active rule backend.

public meta import Iris.ProofMode.Aesop.Rule.Common

public meta section

namespace Iris.ProofMode.Aesop.Rule.Builtin.Identity

open Lean Meta Std
open Iris.BI
open Iris.ProofMode
open Iris.ProofMode.Aesop

variable {Q : Type} [Queue Q]

private partial def splitSepTargets (target : Expr) : Array Expr :=
  let target := target.consumeMData
  if target.getAppFn.constName? == some ``BIBase.sep then
    match target.getAppArgs.toList.reverse with
    | rhs :: lhs :: _ => splitSepTargets lhs ++ splitSepTargets rhs
    | _ => #[target]
  else
    #[target]

private def mkSplitChildren (goal : MVarId) :
    MetaM (Option (Array ChildGoalSpec)) := do
  goal.withContext do
    let goalType ← instantiateMVars (← goal.getType)
    let some irisGoal := parseIrisGoal? goalType
      | return none
    let target ← instantiateMVars irisGoal.goal
    let targets := splitSepTargets target
    if targets.size <= 1 then
      return none
    let tag ← goal.getTag
    some <$> targets.mapM λ target => do
      let irisGoal := { irisGoal with goal := target }
      let goalExpr ← mkFreshExprSyntheticOpaqueMVar (IrisGoal.toExpr irisGoal) tag
      let goal := goalExpr.mvarId!
      return {
        goal
        irisGoal
        mvars := ← goal.getMVarDependencies
      }

def run (input : RuleInput) : SearchM Q RuleOutput := do
  let goal := input.goal
  let state := input.state
  let (some children, postState) ← liftM do
      restoreState state
      let children? ← mkSplitChildren goal
      let postState ← saveState
      return (children?, postState)
    | return {}

  dbg_trace s!"identity split target into {children.size} goals"
  for child in children do
    let targetFmt ← liftM <| ppExpr child.irisGoal.goal
    dbg_trace s!"  identity child target: {targetFmt.pretty}"

  return RuleOutput.single {
    rappState := .unknown
    obunState := .unknown
    obunKind := .managed
    consumedSpatialHyp? := none
    metaState := postState
  } (some <| .contextManagement children (children.map (·.irisGoal)))

end Iris.ProofMode.Aesop.Rule.Builtin.Identity
-/
