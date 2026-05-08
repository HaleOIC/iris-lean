module

public meta import Iris.ProofMode.Aesop.Search.SearchM

public meta section

namespace Iris.ProofMode.Aesop.Search

open Lean Elab Tactic Meta
open Iris.ProofMode.Aesop.Search
open Iris.ProofMode.Aesop.Tree

variable {Q : Type} [Queue Q]

private meta partial def nextActiveGoal : SearchM Q GoalRef := do
  let some gref ← popGoal?
    | throwError "iaesop : internal error: no active goals left"
  if (← (← gref.get).isActive) then
    return gref
  else nextActiveGoal

private meta def expandNextGoal : SearchM Q Unit := do
  let _ ← nextActiveGoal
  -- let result ← expandGoal gref
  -- match result with
  -- | .proved newRapps |

private meta def finalizeProof : SearchM Q Unit := do
  (← getRootMVar).withContext do
    return

/-- Check tree status function set -/
private meta def checkRootProven : SearchM Q Bool := do
  if (← (← getRootGoal).get).state.isProven then
    finalizeProof
    return true
  else
    return false

private meta def checkRootUnprovable : SearchM Q (Option MessageData) := do
  return none

private meta def checkGoalLimit : SearchM Q (Option MessageData) := do
  return none

private meta def checkRappLimit : SearchM Q (Option MessageData) := do
  return none

private meta def checkNonfatalError? : SearchM Q (Option MessageData) := do
  let checks : Array (SearchM Q (Option MessageData)) :=
    #[checkRootUnprovable, checkGoalLimit, checkRappLimit]
  for check in checks do
    if let some err ← check then
      return some err
  return none

private meta def handleNonfatalError (_err : MessageData) : SearchM Q (Array MVarId) := do
  return #[]

-- Main Search loop
private meta partial def searchLoop : SearchM Q (Array MVarId) :=
  withIncRecDepth do
    checkSystem "iaesop"
    if ← checkRootProven then return #[]
    if let some err ← checkNonfatalError? then
      handleNonfatalError err
    else
      expandNextGoal
      incrementIteration
      searchLoop

meta def search (goal : MVarId) (_irisGoal : IrisGoal) (config : SearchConfig := {}) :
    ProofModeM (Array MVarId) := do
  goal.checkNotAssigned `iaesop
  -- TODO: parse ruleset before run search loop
  -- Currently, we only work on the hypothesis in the Hyps
  -- TODO: extend this to support multiple strategy (can parse Q from configuration)
  let (remaining, _, _) ← SearchM.run (Q := BestFirstQueue) config goal do
    searchLoop
  return remaining

end Search
