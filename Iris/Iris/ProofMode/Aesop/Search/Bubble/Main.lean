module

public meta import Lean.Util.Profile
public meta import Iris.ProofMode.Aesop.Rule.Backward.Index
public meta import Iris.ProofMode.Aesop.Rule.Dispatch
public meta import Iris.ProofMode.Aesop.Search.Shared.RuleSelection
public meta import Iris.ProofMode.Aesop.Search.Shared.RuleIndex
public meta import Iris.ProofMode.Aesop.Search.Bubble.Commit
public meta import Iris.ProofMode.Aesop.Search.Bubble.Replay

public meta section

namespace Iris.ProofMode.Aesop.Search.Bubble

open Lean Meta Std
open Iris.ProofMode
open Iris.ProofMode.Aesop

initialize registerTraceClass `iaesop.search.bubble

variable {Q : Type} [Queue Q]

private partial def nextActiveGoal? : BubbleM Q (Option GoalRef) := do
  let some goalRef ← liftM (m := CoreM Q) popGoal?
    | return none
  let goal ← goalRef.get
  if (← goal.isActive) && !(← isGoalExhausted goal.id) then return some goalRef
  nextActiveGoal?

private def runRule (parentRef : GoalRef) (matchResult : RuleMatch) :
    BubbleM Q BubbleRuleResult := do
  let some input ← liftM (m := CoreM Q) <|
      mkRuleInput (toString matchResult.rule.id) parentRef matchResult
    | return .failed
  let output ← liftM (m := CoreM Q) <|
    input.matchResult.rule.info.builder.run input
  let result ← commitRuleOutput parentRef input.matchResult.rule output
  match result with
  | .closed rapps =>
    -- Emit bubbles for closed Rapps upward.
    rapps.forM λ rapp => emitRappBubble rapp #[] #[]
  | .expanded _ | .failed => pure ()
  return result

private partial def runFirstRule (parentRef : GoalRef) : BubbleM Q BubbleRuleResult := do
  let candidates ← liftM (m := CoreM Q) <| selectRules parentRef
  let (remaining, result) ← pickLoop candidates
  parentRef.modify fun goal => goal.setRulesQueue remaining
  if remaining.isEmpty then
    markGoalExhausted (← parentRef.get).id
  return result
where
  pickLoop (queue : RuleQueue) : BubbleM Q (RuleQueue × BubbleRuleResult) := do
    let some (matchResult, remaining) := RuleQueue.pop? queue
      | return (queue, .failed)
    let result ← runRule parentRef matchResult
    match result with
    | .closed .. | .expanded .. => return (remaining, result)
    | .failed => pickLoop remaining

private def expandGoal (goalRef : GoalRef) : BubbleM Q BubbleRuleResult := do
  if !(← (← goalRef.get).isNormalized) then
    liftM (m := CoreM Q) <| normalizeGoal goalRef
  if (← goalRef.get).normalizationState.isProvenByNorm then
    emitNormalizationBubble goalRef
    markGoalExhausted (← goalRef.get).id
    return .closed #[]
  runFirstRule goalRef

private def expandNextGoal : BubbleM Q Bool := do
  let some goalRef ← nextActiveGoal? | return false
  let result ← expandGoal goalRef
  let iteration ← liftM (m := Aesop.CoreM Q) getIteration
  goalRef.modify fun goal => goal.setLastExpandedInIteration iteration
  let goal ← goalRef.get
  if (← goal.isActive) && !(← isGoalExhausted goal.id) then
    liftM (m := CoreM Q) <| enqueueGoals #[goalRef]
  match result with
  | .failed | .closed .. | .expanded .. => pure ()
  return true

private def Goal.currentMVar? (goal : Goal) : Option MVarId :=
  if goal.state.isProven then none
  else match goal.normalizationState with
    | .notNormal => some goal.preNormGoal
    | .normal postGoal .. => some postGoal
    | .provenByNorm .. => none

private partial def searchLoop : BubbleM Q (Array MVarId) := do
  checkSystem "iaesop(bubble)"
  if let some rootBubble ← getRootSolution? then
    return ← replayProof rootBubble
  if ← expandNextGoal then
    liftM (m := Aesop.CoreM Q) incrementIteration
    searchLoop
  -- [TODO] Not sure what does the following function do?
  -- else if ← spawnBlockedLinearResidualGroups then
  --   searchLoop
  else
    -- Collect the remaining goals
    let outerState ← liftM (m := CoreM Q) <| getThe $ CoreM.State Q
    let queued ← Queue.toArray outerState.queue
    let refs ← if queued.isEmpty then pure #[← liftM getRootGoal]
      else pure queued
    refs.foldlM (init := #[]) λ goals goalRef => do
      return goals ++ (Goal.currentMVar? (← goalRef.get)).toArray

meta def search (goal : MVarId) (config : SearchConfig := {}) :
    ProofModeM (Array MVarId) := do
  goal.checkNotAssigned `iaesop
  -- Provide enough budget for configured search depth
  let config := {
    config with maxNormIterations := max config.maxNormIterations config.maxDepth
  }
  -- Construct full ruleIndex from common, backward, and local ones
  let ruleIndex :=
    (commonRuleIndex.merge (← backwardRuleIndex)).merge
      (← Shared.localTheoremRuleIndex config.localTheoremRules)
  -- Run with the specified strategy
  Queue.withStrategy config.strategy fun Q => do
    let (remaining, _, _) ← CoreM.run config ruleIndex goal do
      let (remaining, _) ← (searchLoop (Q := Q)).run {}
      return remaining
    return remaining

end Iris.ProofMode.Aesop.Search.Bubble
