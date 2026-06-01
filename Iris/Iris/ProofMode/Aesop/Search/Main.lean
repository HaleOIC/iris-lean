module

public meta import Iris.ProofMode.Aesop.Search.Configure
public meta import Iris.ProofMode.Aesop.Search.SearchM
public meta import Iris.ProofMode.Aesop.Search.Expansion
public meta import Iris.ProofMode.Aesop.Search.Propogation
public meta import Iris.ProofMode.Aesop.Search.Settlement
public meta import Iris.ProofMode.Aesop.Search.Finalization
public meta import Iris.ProofMode.Aesop.Search.Replay
public meta import Iris.ProofMode.Aesop.Rule.Backward.Main
-- Temporarily disabled while the common rule set is the only active backend.
-- public meta import Iris.ProofMode.Aesop.Rule.Builtin.Main

public meta section

namespace Iris.ProofMode.Aesop.Search

open Lean Elab Tactic Meta Qq Std
open Iris.ProofMode
open Iris.BI

variable {Q : Type} [Queue Q]

private meta partial def nextActiveGoal? : SearchM Q (Option GoalRef) := do
  let some gref ← popGoal?
    | return none
  if (← (← gref.get).isActive) then
    return some gref
  else nextActiveGoal?

private meta def expandNextGoal : SearchM Q Bool := do
  let some gref ← nextActiveGoal?
    | return false
  let result ← expandGoal gref
  let currentIteration ← getIteration
  gref.modify λ g => g.setLastExpandedInIteration currentIteration
  if ← (← gref.get).isActive then enqueueGoals #[gref]
  match result with
  | .failed => pure ()
  | .proved newRapps | .succeeded newRapps =>
    for rref in newRapps do
      -- [Note]: Trace some information here about new generated Rapps
      let _ ← rref.get

  /- Check whether new goal's obun child is proven and collected back -/
  if let some rref ← (← gref.get).children.findM? λ r => do
    return (← r.get).state.isProven
  then Baseline.settleFromRapp rref

  if (← gref.get).state.isProven && !(← readThe SearchM.Context).config.baseline? then
    propogateFromGoal gref
  return true

private meta def Goal.currentMVar? (g : Goal) : Option MVarId :=
  if g.state.isProven then
    none
  else
    match g.normalizationState with
    | .notNormal => some g.preNormGoal
    | .normal postGoal .. => some postGoal
    | .provenByNorm .. => none

private meta def collectRemainingGoals : SearchM Q (Array MVarId) := do
  let queuedGoals ← Queue.toArray (← getThe (SearchM.State Q)).queue
  let refs ←
    if queuedGoals.isEmpty then
      pure #[← getRootGoal]
    else
      pure queuedGoals
  refs.foldlM (init := #[]) λ goals gref => do
    let g ← gref.get
    return goals ++ (Goal.currentMVar? g).toArray

/-- Check tree status function set -/
private meta def checkRootProven : SearchM Q Bool := do
  let rootRef := ← getRootGoal
  if (← rootRef.get).state.isProven then
    traceTreeBeforeReplay
    if (← readThe SearchM.Context).config.baseline? then
      Baseline.replayProof
    else
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

/- [Note] Release the restriction from depth factor -/
private meta partial def searchLoop : SearchM Q (Array MVarId) := do
  checkSystem "iaesop"
  if ← checkRootProven then return #[]
  if let some err ← checkNonfatalError? then
    handleNonfatalError err
  else
    if ← expandNextGoal then
      incrementIteration
      searchLoop
    else
      collectRemainingGoals

meta def search (goal : MVarId) (config : SearchConfig := {}) :
    ProofModeM (Array MVarId) := do
  goal.checkNotAssigned `iaesop
  let ruleIndex := commonRuleIndex.merge (← backwardRuleIndex)
  Queue.withStrategy config.strategy λ Q => do
    let (remaining, _, _) ← SearchM.run (Q := Q) config ruleIndex goal do
      searchLoop
    return remaining

end Search
