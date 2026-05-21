module

public meta import Iris.ProofMode.Aesop.Search.SearchM
public meta import Iris.ProofMode.Aesop.Search.Types

public meta section

namespace Iris.ProofMode.Aesop.Search

variable {Q : Type} [Queue Q]

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

private def markOtherRappsIrrelevant
    (goalRef : GoalRef) (keepRappRef : RappRef) : SearchM Q Unit := do
  let keepId := (← keepRappRef.get).id
  for rref in (← goalRef.get).children do
    if (← rref.get).id != keepId then
      markRappIrrelevant rref

private def writeSplit
    (minSize : Nat) (splits : Array (Array IrisHyp))
    (idx : Nat) (hyps : Array IrisHyp) : Array (Array IrisHyp) :=
  let size := max minSize (idx + 1)
  (List.range size).foldl (init := #[]) λ acc j =>
    acc.push <| if idx == j then hyps else splits[j]?.getD #[]

private def markOtherGoalsIrrelevant
    (obunRef : ObunRef) (keepId : GoalId) : SearchM Q Unit := do
  for gref in (← obunRef.get).goals do
    if (← gref.get).id != keepId then
      markGoalIrrelevant gref

mutual

private meta partial def propogateFromGoal (gref : GoalRef)
    (cur : Array IrisHyp) (fixed : Array (Array IrisHyp)) : SearchM Q Unit := do
  let g ← gref.get
  if !g.state.isProven then
    throwError "iaesop(baseline): unproved goal should not be propagated"

  let obunRef := g.parent
  let obun ← obunRef.get
  if obun.state.isProven then
    return
  if obun.id == .zero then
    obunRef.modify λ o => o.setState .proven
    return
  let idx? ←
    if obun.kind.isPlain then
      if obun.goals.size > 1 then
        throwError "iaesop(baseline): multiple goals plain obun is not supported"
      else
        pure none
    else
      let some caseId := g.caseId?
        | throwError s!"iaesop(baseline): non-plain goal {g.id} does not have a split case id"
      pure (some caseId.toNat)
  markOtherGoalsIrrelevant obunRef g.id
  obunRef.modify λ o => o.setState .proven
  propogateFromObun obunRef idx? cur fixed

private meta partial def propogateFromObun (obunRef : ObunRef)
    (idx? : Option Nat) (cur : Array IrisHyp) (fixed : Array (Array IrisHyp)) :
    SearchM Q Unit := do
  let obun ← obunRef.get
  if !obun.state.isProven then
    throwError "iaesop(baseline): unproved obun should not be propogated"

  /- Already reached the root, just return -/
  let some rappRef := obun.parent?
    | return
  let rapp ← rappRef.get
  if !rapp.state.isProven then
    rappRef.modify λ r => r.setState .proven

  /- Save the used hypothesis or finalize the split case -/
  match obun.kind with
  | .plain => propogateFromRapp rappRef cur fixed
  | .inherited .. =>
    let some idx := idx?
      | throwError "iaesop(baseline): inherited obun proven by goal without case id"
    let onemoreFixed := writeSplit fixed.size fixed idx cur
    propogateFromRapp rappRef #[] onemoreFixed
  | .managed =>
    let some idx := idx?
      | throwError "iaesop(baseline): managed obun proven by goal without case id"
    let finalSplit := writeSplit obun.fullContextIrisSubgoals.size fixed idx cur
    rappRef.modify λ r => r.setFinalizedSpatialSplits finalSplit
    propogateFromRapp rappRef #[] #[]

private meta partial def propogateFromRapp (rappRef : RappRef)
    (cur : Array IrisHyp) (fixed : Array (Array IrisHyp)) : SearchM Q Unit := do
  let rapp ← rappRef.get
  if !rapp.state.isProven then
    throwError "iaesop(baseline): unproved rapp should not be propagated"

  let parentRef := rapp.parent
  markOtherRappsIrrelevant parentRef rappRef
  let used :=
    rapp.finalizedSpatialSplits.foldl
      (init := rapp.consumedSpatialHyp?.toArray) λ acc hyps => acc ++ hyps
  let cur := cur ++ used
  parentRef.modify λ g => g.setState (.provenByRuleApplication cur)
  propogateFromGoal parentRef cur fixed

end

/- Baseline propogation stage starts from rapp -/
public meta partial def baselinePropogateProvenFromRapp
    (rref : RappRef) : SearchM Q Unit :=
  propogateFromRapp rref #[] #[]

end Iris.ProofMode.Aesop.Search
