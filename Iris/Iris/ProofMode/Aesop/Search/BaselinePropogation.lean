module

public meta import Iris.ProofMode.Aesop.Search.SearchM
public meta import Iris.ProofMode.Aesop.Search.Types

public meta section

namespace Iris.ProofMode.Aesop.Search

variable {Q : Type} [Queue Q]

private def allGoalsProven (goals : Array GoalRef) : SearchM Q Bool := do
  goals.allM λ gref => return (← gref.get).state.isProven

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

mutual

private meta partial def propogateFromGoal (gref : GoalRef) : SearchM Q Unit := do
  let g ← gref.get
  if !g.state.isProven then
    throwError "iaesop: internal error : unproved goal should not be propagated"

  let obunRef := g.parent
  let obun ← obunRef.get
  if obun.state.isProven then
    return
  if ← allGoalsProven obun.goals then
    obunRef.modify λ o => o.setState .proven
    propogateFromObun obunRef

private meta partial def propogateFromObun (obunRef : ObunRef) : SearchM Q Unit := do
  let obun ← obunRef.get
  if !obun.state.isProven then
    throwError "iaesop: internal error : unproved obun should not be propogated"

  let some rappRef := obun.parent?
    | return
  let rapp ← rappRef.get
  if rapp.state.isProven then
    return
  rappRef.modify λ r => r.setState .proven
  propogateFromRapp rappRef

private meta partial def propogateFromRapp (rappRef : RappRef) : SearchM Q Unit := do
  let rapp ← rappRef.get
  if !rapp.state.isProven then
    throwError "iaesop: internal error: unproved rapp should not be propagated"

  let parentRef := rapp.parent
  markOtherRappsIrrelevant parentRef rappRef
  parentRef.modify λ g =>
    g.setState (.provenByRuleApplication rapp.consumedSpatialHyp?.toArray)
  propogateFromGoal parentRef

end

public meta partial def baselinePropogateProvenFromRapp
    (rref : RappRef) : SearchM Q Unit :=
  propogateFromRapp rref

end Iris.ProofMode.Aesop.Search
