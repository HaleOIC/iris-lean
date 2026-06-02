module

public meta import Iris.ProofMode.Aesop.Search.SearchM
public meta import Iris.ProofMode.Aesop.Search.Types

public meta section

namespace Iris.ProofMode.Aesop.Baseline

variable {Q : Type} [Queue Q]

initialize Lean.registerTraceClass `iaesop.settlement

inductive Hyp where
  | generated (hyp : IrisHyp)
  | consumed (hyp : IrisHyp)
  deriving Inhabited

def netConsumedHyps (events : Array Hyp) : Array IrisHyp :=
  events.foldl (init := #[]) λ acc event =>
    match event with
    | .generated hyp =>
      acc.filter λ used => used.name != hyp.name
    | .consumed hyp =>
      acc.push hyp

private def formatList (xs : List String) : String :=
  match xs with
  | [] => "[]"
  | x :: xs => "[" ++ xs.foldl (λ acc x => acc ++ ", " ++ x) x ++ "]"

private def formatHyps (hyps : Array IrisHyp) : String :=
  formatList <| hyps.toList.map toString

private def formatCase? : Option CaseId → String
  | some caseId => toString caseId
  | none => "none"

private def formatHypEvent : Hyp → String
  | .generated hyp => s!"generated {hyp}"
  | .consumed hyp => s!"consumed {hyp}"

private def formatHypEvents (hyps : Array Hyp) : String :=
  formatList <| hyps.toList.map formatHypEvent

private def formatAppliedHyps (hyps : Array AppliedHyp) : String :=
  formatList <| hyps.toList.map toString

private def formatMarks (marks : Array (Nat × Nat)) : String :=
  formatList <| marks.toList.map λ (depth, pos) => s!"({depth}, {pos})"

private def formatSplit (split : Array (Array IrisHyp)) : String :=
  formatList <| split.toList.map formatHyps

/- Core data structure tracking generated and consumed spatial Iris hypotheses. -/
private structure HypLog where
  path : MarkedLog Hyp := default
  byCase : Std.HashMap ObunId (Array (CaseId × Array IrisHyp)) := {}
  deriving Inhabited

namespace HypLog

private def pushMany (state : HypLog) (hyps : Array Hyp) : HypLog :=
  { state with path := state.path.pushMany hyps }

private def summary (state : HypLog) : String :=
  s!"entries={formatHypEvents state.path.entries}, marks={formatMarks state.path.marks}"

private def collect (state : HypLog) (depth : Nat) :
    Array IrisHyp × HypLog :=
  let (hyps, path) := state.path.collect depth
  (netConsumedHyps hyps, { state with path })

private def insertCase
    (state : HypLog) (obunId : ObunId) (caseId : CaseId)
    (hyps : Array IrisHyp) : HypLog :=
  let old := match state.byCase.get? obunId with
    | some entries => entries
    | none => #[]
  { state with byCase := state.byCase.insert obunId (old ++ [(caseId, hyps)]) }

private def finalizedSplit (state : HypLog) (obunId : ObunId) : Array (Array IrisHyp) :=
  let entries := match state.byCase.get? obunId with
    | some entries => entries
    | none => #[]
  (entries.qsort λ x y => decide (x.1.toNat < y.1.toNat)).map λ entry => entry.2

end HypLog

mutual

private meta partial def markGoalIrrelevant (gref : GoalRef) : SearchM Q Unit := do
  let g ← gref.get
  if g.isIrrelevant then
    return
  trace[iaesop.settlement] s!"iaesop.settlement: mark goal {g.id} irrelevant"
  gref.modify λ g => g.setIsIrrelevant true
  for rref in g.children do
    markRappIrrelevant rref

private meta partial def markRappIrrelevant (rref : RappRef) : SearchM Q Unit := do
  let r ← rref.get
  if r.isIrrelevant then
    return
  trace[iaesop.settlement] s!"iaesop.settlement: mark rapp {r.id} irrelevant"
  rref.modify λ r => r.setIsIrrelevant true
  markObunIrrelevant r.children

private meta partial def markObunIrrelevant (oref : ObunRef) : SearchM Q Unit := do
  let o ← oref.get
  if o.isIrrelevant then
    return
  trace[iaesop.settlement] s!"iaesop.settlement: mark obun {o.id} irrelevant"
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
    (hypLog : HypLog) : SearchM Q Unit := do
  let goal ← gref.get
  trace[iaesop.settlement] s!"iaesop.settlement: settle goal {goal.id}, state={goal.state}, \
    case={formatCase? goal.caseId?}, log={hypLog.summary}"
  if !goal.state.isProven then
    throwError "iaesop(baseline): unproved goal should not be propagated"

  /- Mark other goals irrelevant, and only keep current goal's id -/
  let obunRef := goal.parent
  let obun ← obunRef.get
  trace[iaesop.settlement] s!"iaesop.settlement: goal {goal.id} propagates to obun {obun.id}"
  (← obunRef.get).goals.forM λ gref => do
    if (← gref.get).id != goal.id then
      markGoalIrrelevant gref

  /- Bring current caseId up to Obun -/
  obunRef.modify λ o => o.setState .proven
  let consumedHyps := goal.normalizationState.usedSpatialHyps.map λ hyp => .consumed hyp
  let generatedHyps := goal.normalizationState.generatedSpatialHyps.map λ hyp => .generated hyp
  trace[iaesop.settlement] s!"iaesop.settlement: goal {goal.id} norm generated=\
    {formatHypEvents generatedHyps}, consumed={formatHypEvents consumedHyps}"
  settleObun obunRef goal.caseId? $ hypLog.pushMany generatedHyps |>.pushMany consumedHyps

private meta partial def settleObun (obunRef : ObunRef)
    (caseId? : Option CaseId) (usedHyps : HypLog) :
    SearchM Q Unit := do
  let obun ← obunRef.get
  trace[iaesop.settlement] s!"iaesop.settlement: settle obun {obun.id}, state={obun.state}, \
    kind={obun.kind}, depth={obun.contextDepth}, case={formatCase? caseId?}, log={usedHyps.summary}"
  if !obun.state.isProven then
    throwError "iaesop(baseline): unproved obun should not be propogated"

  /- Already reached the root, just return -/
  let some rappRef := obun.parent?
    | trace[iaesop.settlement] s!"iaesop.settlement: obun {obun.id} is root, settlement done"
      return

  /- Mark rapp proven -/
  let rapp ← rappRef.get
  if !rapp.state.isProven then
    trace[iaesop.settlement] s!"iaesop.settlement: mark parent rapp {rapp.id} proven"
    rappRef.modify λ r => r.setState .proven

  /- Save the used hypothesis or finalize the split case -/
  match obun.kind with
  | .plain =>
    trace[iaesop.settlement] s!"iaesop.settlement: obun {obun.id} is plain, propagate to rapp {rapp.id}"
    settleRapp rappRef usedHyps
  | .inherited source _ =>
    let some caseId := caseId?
      | throwError "iaesop(baseline): inherited obun proven by goal without case id"
    let (cur, usedHyps) := usedHyps.collect obun.contextDepth
    trace[iaesop.settlement] s!"iaesop.settlement: obun {obun.id} inherited collect depth \
      {obun.contextDepth}, case={caseId}, cur={formatHyps cur}, log={usedHyps.summary}"
    let usedHyps := usedHyps.insertCase source caseId cur
    trace[iaesop.settlement] s!"iaesop.settlement: obun {obun.id} inserts case {caseId} \
      into source obun {source}"
    settleRapp rappRef usedHyps
  | .managed | .duplicated =>
    let some caseId := caseId?
      | throwError "iaesop(baseline): managed obun proven by goal without case id"
    let (cur, usedHyps) := usedHyps.collect obun.contextDepth
    trace[iaesop.settlement] s!"iaesop.settlement: obun {obun.id} local collect depth \
      {obun.contextDepth}, case={caseId}, cur={formatHyps cur}, log={usedHyps.summary}"
    let usedHyps := usedHyps.insertCase obun.id caseId cur
    let finalized := usedHyps.finalizedSplit obun.id
    trace[iaesop.settlement] s!"iaesop.settlement: obun {obun.id} finalized splits \
      {formatSplit finalized}"
    obunRef.modify λ o => o.setFinalizedSpatialSplits finalized
    settleRapp rappRef usedHyps

private meta partial def settleRapp (rappRef : RappRef) (hypLog : HypLog) : SearchM Q Unit := do
  let rapp ← rappRef.get
  trace[iaesop.settlement] s!"iaesop.settlement: settle rapp {rapp.id}, state={rapp.state}, \
    rule={rapp.appliedRule.id}, log={hypLog.summary}"
  if !rapp.state.isProven then
    throwError "iaesop(baseline): unproved rapp should not be propagated"

  /- Mark other Rapps irrelevant, only keep current rapp's id -/
  let goalRef := rapp.parent
  let parentGoal ← goalRef.get
  trace[iaesop.settlement] s!"iaesop.settlement: rapp {rapp.id} propagates to goal {parentGoal.id}"
  (← goalRef.get).children.forM λ rref => do
    if (← rref.get).id != rapp.id then
      markRappIrrelevant rref

  /- Collect used Hypothesis for this rapp -/
  let consumedHyps := rapp.consumedSpatialHyps.map .consumed
  let generatedHyps := rapp.generatedSpatialHyps.map .generated
  trace[iaesop.settlement] s!"iaesop.settlement: rapp {rapp.id} used={formatAppliedHyps rapp.usedHyps}, \
    generated={formatHypEvents generatedHyps}, consumed={formatHypEvents consumedHyps}"
  goalRef.modify λ g => g.setState .provenByRuleApplication
  settleGoal goalRef $ hypLog.pushMany generatedHyps |>.pushMany consumedHyps

end

/- (Baseline) settlement entry point for a proven rule application. -/
partial def settleFromRapp
    (rref : RappRef) : SearchM Q Unit := do
  trace[iaesop.settlement] "iaesop.settlement: start from rapp"
  settleRapp rref default
