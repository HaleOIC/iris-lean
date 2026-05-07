module

public meta import Iris.ProofMode.Aesop.Tree.Basic
public import Iris.ProofMode.Aesop.Util.Percent
public meta import Batteries.Data.BinomialHeap.Basic

public meta section

namespace Iris.ProofMode.Aesop.Search

open Lean Tree
open Iris.ProofMode.Aesop.Util
open Batteries (BinomialHeap)

class Queue (Q : Type) where
  init : BaseIO Q
  addGoals : Q → Array GoalRef → BaseIO Q
  popGoal : Q → BaseIO (Option GoalRef × Q)

namespace Queue

def init' [Queue Q] (grefs : Array GoalRef) : BaseIO Q := do
  addGoals (← init) grefs

end Queue

namespace BestFirstQueue

structure ActiveGoal where
  goal : GoalRef
  priority : Percent
  lastExpandedInIteration : Iteration
  addedInIteration : Iteration

namespace ActiveGoal

protected def le (g h : ActiveGoal) : Bool :=
  g.priority > h.priority ||
    (g.priority == h.priority &&
      (g.lastExpandedInIteration < h.lastExpandedInIteration ||
        (g.lastExpandedInIteration == h.lastExpandedInIteration &&
          g.addedInIteration ≤ h.addedInIteration)))

protected meta def fromGoalRef (gref : GoalRef) : BaseIO ActiveGoal := do
  let g ← gref.get
  return {
    goal := gref
    -- TODO: consider about the probability (consider involving unassigned variables)
    priority := g.successProbability
    lastExpandedInIteration := g.lastExpandedInIteration
    addedInIteration := g.addedInIteration
  }

end ActiveGoal

end BestFirstQueue

abbrev BestFirstQueue :=
  BinomialHeap BestFirstQueue.ActiveGoal BestFirstQueue.ActiveGoal.le

meta instance : Queue BestFirstQueue where
  init := pure <| BinomialHeap.empty
  addGoals q grefs := grefs.foldlM (init := q) λ q gref =>
    return BinomialHeap.insert (← BestFirstQueue.ActiveGoal.fromGoalRef gref) q
  popGoal q := pure <|
    match q.deleteMin with
    | none => (none, q)
    | some (ag, q) => (some ag.goal, q)

structure LIFOQueue where
  goals : Array GoalRef

meta instance : Queue LIFOQueue where
  init := pure <| ⟨#[]⟩
  addGoals q grefs := pure <| ⟨q.goals ++ grefs.reverse⟩
  popGoal q := pure <|
    match q.goals.back? with
    | none => (none, q)
    | some g => (some g, ⟨q.goals.pop⟩)

structure FIFOQueue where
  goals : Array GoalRef
  pos : Nat

meta instance : Queue FIFOQueue where
  init := pure <| ⟨#[], 0⟩
  addGoals q grefs := pure <| ⟨q.goals ++ grefs, q.pos⟩
  popGoal q := pure <|
    if h: q.pos < q.goals.size then
      (some q.goals[q.pos], ⟨q.goals, q.pos + 1⟩)
    else (none, q)

-- TODO: add a function here to return a corresponding instance
-- according to the strategy given by option

end Search
