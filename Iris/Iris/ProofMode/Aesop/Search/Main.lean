module

public meta import Iris.ProofMode.Aesop.Search.Configure
public meta import Iris.ProofMode.Aesop.Search.SearchM
public meta import Iris.ProofMode.Aesop.Search.Expansion
public meta import Iris.ProofMode.Aesop.Search.Settlement
public meta import Iris.ProofMode.Aesop.Search.Replay
public meta import Iris.ProofMode.Aesop.Rule.Backward.Index

public meta section

namespace Iris.ProofMode.Aesop.Search

open Lean Elab Tactic Meta Qq Std
open Iris.ProofMode
open Iris.BI

variable {Q : Type} [Queue Q]

private meta def localTheoremRuleIndex (rules : Array LocalTheoremRule) :
    MetaM (Index RuleInfo) := do
  let mut idx : Index RuleInfo := {}
  let mut traceEntries : Array String := #[]
  for localRule in rules do
    match localRule.kind with
    | .backward =>
        let rule ← Rule.Backward.mkBackwardRule
          localRule.decl localRule.successProbability .local
        traceEntries := traceEntries.push
          s!"backward {localRule.decl} ({localRule.successProbability}): {toString (format rule.indexingMode)}"
        idx := idx.add rule rule.indexingMode
    | .forward =>
        throwError "iaesop: local forward theorem rules are not implemented yet"
    | kind =>
        throwError "iaesop: local theorem rule kind '{kind}' is not supported"
  unless rules.isEmpty do
    trace[iaesop.ruleIndex] s!"iaesop: generated local theorem index with {rules.size} rules"
    traceEntries.forM λ entry => do
      trace[iaesop.ruleIndex] s!"  {entry}"
  return idx

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

private meta def lazyStepsToScript (ruleName : DisplayRuleId)
    (steps? : Option (Array Script.LazyStep)) : SearchM Q Script.UScript := do
  let some steps := steps?
    | throwError "iaesop?: tactic script generation is not supported by rule {ruleName}"
  return steps

mutual
  private meta partial def extractScriptFromGoal (gref : GoalRef) :
      SearchM Q Script.UScript := do
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
      SearchM Q Script.UScript := do
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
private meta def checkRootProven : SearchM Q Bool := do
  let rootRef := ← getRootGoal
  if (← rootRef.get).state.isProven then
    traceTreeBeforeReplay
    Baseline.replayProof
    let config := (← readThe SearchM.Context).config
    unless config.generateScript? do return true
    let rootRef ← getRootGoal
    let root ← rootRef.get
    let script ← extractScriptFromGoal rootRef
    let tacs ← liftM <| script.render root.preNormGoal
    liftM <| Script.addTryThisTacticSeqSuggestion (← getRef) tacs
    return true
  else
    return false

/- [Note] Release the restriction from depth factor -/
private meta partial def searchLoop : SearchM Q (Array MVarId) := do
  checkSystem "iaesop"
  if ← checkRootProven then return #[]
  if ← expandNextGoal then
    incrementIteration
    searchLoop
  else
    collectRemainingGoals

meta def search (goal : MVarId) (config : SearchConfig := {}) :
    ProofModeM (Array MVarId) := do
  goal.checkNotAssigned `iaesop
  let ruleIndex :=
    (commonRuleIndex.merge (← backwardRuleIndex)).merge
      (← localTheoremRuleIndex config.localTheoremRules)
  Queue.withStrategy config.strategy λ Q => do
    let (remaining, _, _) ← SearchM.run (Q := Q) config ruleIndex goal do
      searchLoop
    return remaining

end Search
