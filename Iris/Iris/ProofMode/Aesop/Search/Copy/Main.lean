module

public meta import Iris.ProofMode.Aesop.Search.Shared.Configure
public meta import Iris.ProofMode.Aesop.Search.Shared.RuleIndex
public meta import Iris.ProofMode.Aesop.Search.Shared.CoreM
public meta import Iris.ProofMode.Aesop.Search.Copy.Expansion
public meta import Iris.ProofMode.Aesop.Search.Copy.Settlement
public meta import Iris.ProofMode.Aesop.Search.Copy.Replay
public meta import Iris.ProofMode.Aesop.Rule.Backward.Index

public meta section

namespace Iris.ProofMode.Aesop.Search.Copy

open Lean Elab Tactic Meta Qq Std
open Iris.ProofMode
open Iris.BI
open Iris.ProofMode.Aesop

variable {Q : Type} [Queue Q]

private meta partial def nextActiveGoal? : CoreM Q (Option GoalRef) := do
  let some gref ← popGoal?
    | return none
  if (← (← gref.get).isActive) then
    return some gref
  else nextActiveGoal?

private meta def expandNextGoal : CoreM Q Bool := do
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
  then Copy.settleFromRapp rref

  return true

private meta def Goal.currentMVar? (g : Goal) : Option MVarId :=
  if g.state.isProven then
    none
  else
    match g.normalizationState with
    | .notNormal => some g.preNormGoal
    | .normal postGoal .. => some postGoal
    | .provenByNorm .. => none

private meta def collectRemainingGoals : CoreM Q (Array MVarId) := do
  let queuedGoals ← Queue.toArray (← getThe (CoreM.State Q)).queue
  let refs ←
    if queuedGoals.isEmpty then
      pure #[← getRootGoal]
    else
      pure queuedGoals
  refs.foldlM (init := #[]) λ goals gref => do
    let g ← gref.get
    return goals ++ (Goal.currentMVar? g).toArray

private meta def lazyStepsToScript (ruleName : DisplayRuleId)
    (steps? : Option (Array Script.LazyStep)) : CoreM Q Script.UScript := do
  let some steps := steps?
    | throwError "iaesop?: tactic script generation is not supported by rule {ruleName}"
  return steps

mutual
  private meta partial def extractScriptFromGoal (gref : GoalRef) :
      CoreM Q Script.UScript := do
    let goal ← gref.get
    let normScript ←
      match goal.normalizationState with
      | .notNormal => return #[]
      | .normal (script := script) .. | .provenByNorm (script := script) .. =>
        script.foldlM (init := #[]) λ acc (ruleName, steps?) => do
          let some steps := steps?
            | throwError "iaesop?: tactic script generation is not supported by rule {ruleName}"
          return acc ++ steps
    if goal.normalizationState.isProvenByNorm then
      return normScript
    let some rref ← goal.children.findM? λ rref => do
      let rapp ← rref.get
      return rapp.state.isProven && !rapp.isIrrelevant
      /- The goal is proven but exposes no proven rule application (e.g. closed
      purely by context inheritance); emit only the normalization prefix. -/
      | return normScript
    return normScript ++ (← extractScriptFromRapp rref)

  private meta partial def extractScriptFromRapp (rref : RappRef) :
      CoreM Q Script.UScript := do
    let rapp ← rref.get
    let mut script ← lazyStepsToScript (.ruleId rapp.appliedRule.id) rapp.scriptSteps?
    let obun ← rapp.children.get
    /- Only follow the children on the proven path, mirroring replay; dead or
    irrelevant search branches must not contribute to the script. -/
    for child in obun.goals do
      let childGoal ← child.get
      if childGoal.state.isProven && !childGoal.isIrrelevant then
        script := script ++ (← extractScriptFromGoal child)
    return script
end

/-- Check tree status function set -/
private meta def checkRootProven : CoreM Q (Option (Array MVarId)) := do
  let rootRef := ← getRootGoal
  if (← rootRef.get).state.isProven then
    traceTreeBeforeReplay
    let remainingGoals ← Copy.replayProof
    let config := (← readThe CoreM.Context).config
    unless config.generateScript? do return some remainingGoals
    let rootRef ← getRootGoal
    let root ← rootRef.get
    let script ← extractScriptFromGoal rootRef
    let tacs ← liftM <| script.render root.preNormGoal
    liftM <| Script.addTryThisTacticSeqSuggestion (← getRef) tacs
    return some remainingGoals
  else
    return none

/- [Note] Release the restriction from depth factor -/
private meta partial def searchLoop : CoreM Q (Array MVarId) := do
  checkSystem "iaesop"
  if let some remainingGoals ← checkRootProven then return remainingGoals
  if ← expandNextGoal then
    incrementIteration
    searchLoop
  else
    collectRemainingGoals

/- Both algorithms share the same entry point.-/
meta def search (goal : MVarId) (config : SearchConfig := {}) :
    ProofModeM (Array MVarId) := do
  goal.checkNotAssigned `iaesop
  let config := {
    config with maxNormIterations := max config.maxNormIterations config.maxDepth
  }
  -- Construct rule index for locating valid rule to apply
  let ruleIndex := (commonRuleIndex.merge (← backwardRuleIndex)).merge
    (← Shared.localTheoremRuleIndex config.localTheoremRules)
  Queue.withStrategy config.strategy λ Q => do
    let (remaining, _, _) ← CoreM.run (Q := Q) config ruleIndex goal do
      searchLoop
    return remaining

end Iris.ProofMode.Aesop.Search.Copy
