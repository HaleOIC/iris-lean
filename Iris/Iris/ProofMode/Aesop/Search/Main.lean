module

public meta import Iris.ProofMode.Aesop.Search.SearchM
public meta import Iris.ProofMode.Tactics.Assumption
public meta import Iris.ProofMode.Tactics.Intro
public meta import Iris.ProofMode.Tactics.LeftRight
public meta import Iris.ProofMode.Tactics.ModIntro
public meta import Iris.ProofMode.Tactics.Pure

public meta section

namespace Iris.ProofMode.Aesop

open Lean Elab Tactic Meta
open Iris.ProofMode.Aesop.Search

private meta def basicCandidates (idx : Nat) : TacticM (Array (TSyntax `tactic)) := do
  let h := mkIdent <| (Name.mkSimple "h").appendIndexAfter idx
  let x := mkIdent <| (Name.mkSimple "x").appendIndexAfter idx
  return #[
    ← `(tactic| iassumption),
    ← `(tactic| ipure_intro),
    ← `(tactic| iemp_intro),
    ← `(tactic| imodintro),
    ← `(tactic| iintro #$h:ident),
    ← `(tactic| iintro %$x:ident),
    ← `(tactic| iintro $h:ident),
    ← `(tactic| iintro -),
    ← `(tactic| ileft),
    ← `(tactic| iright)
  ]

private meta def runTacticAt? (mvar : MVarId) (tac : TSyntax `tactic) :
    SearchM (Option (Array MVarId)) := do
  let saved ← liftM Lean.Elab.Tactic.saveState
  try
    let goals ← Lean.Elab.Tactic.run mvar (evalTactic tac) |>.run'
    return some goals.toArray
  catch _ =>
    liftM saved.restore
    return none


private meta def isIrisGoalMVar (goal : MVarId) : SearchM Bool := do
  goal.withContext do
    let goalType ← instantiateMVars (← goal.getType)
    return (parseIrisGoal? goalType).isSome

private meta partial def firstProgress? (goal : MVarId) :
    SearchM (Option (Array MVarId)) := do
  if !(← isIrisGoalMVar goal) then
    return none
  let idx ← SearchM.getIteration
  for tac in (← basicCandidates idx) do
    if let some goals ← runTacticAt? goal tac then
      return some goals
  return none

private meta partial def searchLoop : Nat → SearchM Unit
  | 0 => return
  | fuel + 1 => do
      let some goal ← SearchM.popGoal?
        | return
      if ← goal.isAssignedOrDelayedAssigned then
        SearchM.incrementIteration
        searchLoop fuel
      else
        match ← firstProgress? goal with
        | some goals =>
            SearchM.enqueueGoals goals
            SearchM.incrementIteration
            searchLoop fuel
        | none =>
            SearchM.addStuck goal
            SearchM.incrementIteration
            searchLoop fuel

meta def search (mvar : MVarId) (_irisGoal : IrisGoal) (config : SearchConfig := {}) :
    ProofModeM (Array MVarId) := do
  mvar.checkNotAssigned `iaesop

  let (remaining, _, _) ← SearchM.run config mvar do
    searchLoop config.maxSteps
    SearchM.remainingGoals
  return remaining

end Iris.ProofMode.Aesop
