module

public meta import Iris.ProofMode.Aesop.Search.SearchM
public meta import Iris.ProofMode.Aesop.Search.Types

public meta section

namespace Iris.ProofMode.Aesop.Baseline

variable {Q : Type} [Queue Q]

/- Core data structure, track used spatial Iris Hypotheses -/
private structure UsedHypLog where
  path : MarkedLog IrisHyp
  byCase : Std.HashMap ObunId (Array (CaseId × Array IrisHyp))
  deriving Inhabited

namespace UsedHypLog

private def empty : UsedHypLog where
  path := MarkedLog.empty
  byCase := {}

private def pushMany (state : UsedHypLog) (hyps : Array IrisHyp) : UsedHypLog :=
  { state with path := state.path.pushMany hyps }

private def collect (state : UsedHypLog) (depth : Nat) :
    Array IrisHyp × UsedHypLog :=
  let (hyps, path) := state.path.collect depth
  (hyps, { state with path })

private def insertCase
    (state : UsedHypLog) (obunId : ObunId) (caseId : CaseId)
    (hyps : Array IrisHyp) : UsedHypLog :=
  let old := match state.byCase.get? obunId with
    | some entries => entries
    | none => #[]
  { state with byCase := state.byCase.insert obunId (old ++ [(caseId, hyps)]) }

private def finalizedSplit (state : UsedHypLog) (obunId : ObunId) : Array (Array IrisHyp) :=
  let entries := match state.byCase.get? obunId with
    | some entries => entries
    | none => #[]
  (entries.qsort λ x y => decide (x.1.toNat < y.1.toNat)).map λ entry => entry.2

end UsedHypLog

mutual

private meta partial def markGoalIrrelevant (gref : GoalRef) : SearchM Q Unit := do
  let g ← gref.get
  if g.isIrrelevant then
    return
  gref.modify λ g => g.setIsIrrelevant true
  for rref in g.children do
    markRappIrrelevant rref

private meta partial def markRappIrrelevant (rref : RappRef) : SearchM Q Unit := do
  let r ← rref.get
  if r.isIrrelevant then
    return
  rref.modify λ r => r.setIsIrrelevant true
  markObunIrrelevant r.children

private meta partial def markObunIrrelevant (oref : ObunRef) : SearchM Q Unit := do
  let o ← oref.get
  if o.isIrrelevant then
    return
  oref.modify λ o => o.setIsIrrelevant true
  for gref in o.goals do
    markGoalIrrelevant gref

end

private def markOtherGoalsIrrelevant
    (obunRef : ObunRef) (keepId : GoalId) : SearchM Q Unit := do
  for gref in (← obunRef.get).goals do
    if (← gref.get).id != keepId then
      markGoalIrrelevant gref

mutual

private meta partial def settleGoal (gref : GoalRef)
    (usedHyps : UsedHypLog) : SearchM Q Unit := do
  let goal ← gref.get
  if !goal.state.isProven then
    throwError "iaesop(baseline): unproved goal should not be propagated"

  /- Mark other goals irrelevant, and only keep current goal's id -/
  let obunRef := goal.parent
  (← obunRef.get).goals.forM λ gref => do
    if (← gref.get).id != goal.id then
      markGoalIrrelevant gref

  /- Bring current caseId up to Obun -/
  obunRef.modify λ o => o.setState .proven
  settleObun obunRef goal.caseId? usedHyps

private meta partial def settleObun (obunRef : ObunRef)
    (caseId? : Option CaseId) (usedHyps : UsedHypLog) :
    SearchM Q Unit := do
  let obun ← obunRef.get
  if !obun.state.isProven then
    throwError "iaesop(baseline): unproved obun should not be propogated"

  /- Already reached the root, just return -/
  let some rappRef := obun.parent?
    | return

  /- Mark rapp proven -/
  let rapp ← rappRef.get
  if !rapp.state.isProven then
    rappRef.modify λ r => r.setState .proven

  /- Save the used hypothesis or finalize the split case -/
  match obun.kind with
  | .plain => settleRapp rappRef usedHyps
  | .inherited source _ =>
    let some caseId := caseId?
      | throwError "iaesop(baseline): inherited obun proven by goal without case id"
    let (cur, usedHyps) := usedHyps.collect obun.contextDepth
    let usedHyps := usedHyps.insertCase source caseId cur
    settleRapp rappRef usedHyps
  | .managed | .duplicated =>
    let some caseId := caseId?
      | throwError "iaesop(baseline): managed obun proven by goal without case id"
    let (cur, usedHyps) := usedHyps.collect obun.contextDepth
    let usedHyps := usedHyps.insertCase obun.id caseId cur
    obunRef.modify λ o => o.setFinalizedSpatialSplits $ usedHyps.finalizedSplit obun.id
    settleRapp rappRef usedHyps

private meta partial def settleRapp (rappRef : RappRef)
    (usedHyps : UsedHypLog) : SearchM Q Unit := do
  let rapp ← rappRef.get
  if !rapp.state.isProven then
    throwError "iaesop(baseline): unproved rapp should not be propagated"

  /- Mark other Rapps irrelevant, only keep current rapp's id -/
  let goalRef := rapp.parent
  (← goalRef.get).children.forM λ rref => do
    if (← rref.get).id != rapp.id then
      markRappIrrelevant rref

  /- Collect used Hypothesis for this rapp -/
  let usedHyps := usedHyps.pushMany rapp.consumedSpatialHyp?.toArray
  goalRef.modify λ g => g.setState .provenByRuleApplication
  settleGoal goalRef usedHyps

end

/- (Baseline) settlement entry point for a proven rule application. -/
public meta partial def settleFromRapp
    (rref : RappRef) : SearchM Q Unit :=
  settleRapp rref UsedHypLog.empty
