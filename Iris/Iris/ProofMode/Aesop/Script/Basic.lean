module

public meta import Lean.Elab.Tactic
public meta import Lean.Meta.Tactic.TryThis
public import Batteries.Tactic.PermuteGoals

public meta section

open Lean Lean.Meta Lean.Elab.Tactic
open Lean.Parser.Tactic (tacticSeq)

namespace Iris.ProofMode.Aesop.Script

private def mkOneBasedNumLit (n : Nat) : NumLit :=
  Syntax.mkNumLit $ toString $ n + 1

private def mkPickGoal (goalPos : Nat) : MetaM (TSyntax `tactic) := do
  let posLit := mkOneBasedNumLit goalPos
  `(tactic| pick_goal $posLit:num)

structure LazyStep where
  preState : Meta.SavedState
  preGoal : MVarId
  tactic : TSyntax `tactic
  postState : Meta.SavedState
  postGoals : Array MVarId

abbrev UScript := Array LazyStep

structure TacticState where
  goals : Array MVarId

namespace TacticState

def getVisibleGoalIndex (s : TacticState) (goal : MVarId) : MetaM Nat := do
  let some idx := s.goals.idxOf? goal
    | throwError "iaesop?: script rendering could not find goal {goal.name}"
  return idx

def pickGoal (s : TacticState) (idx : Nat) : TacticState :=
  if idx == 0 then
    s
  else
    match s.goals[idx]? with
    | some goal =>
        { goals :=
            #[goal] ++ s.goals.extract 0 idx ++
              s.goals.extract (idx + 1) s.goals.size }
    | none => s

def applyStepAtHead (s : TacticState) (step : LazyStep) : TacticState :=
  { goals := step.postGoals ++ s.goals.extract 1 s.goals.size }

def applyStep (s : TacticState) (step : LazyStep) : MetaM TacticState := do
  let idx ← s.getVisibleGoalIndex step.preGoal
  return (s.pickGoal idx).applyStepAtHead step

end TacticState

namespace LazyStep

def render (acc : Array (TSyntax `tactic)) (step : LazyStep)
    (tacticState : TacticState) :
    MetaM (Array (TSyntax `tactic) × TacticState) := do
  let pos ← tacticState.getVisibleGoalIndex step.preGoal
  let tacticState ← tacticState.applyStep step
  let acc ←
    if pos == 0 then
      pure acc
    else
      pure (acc.push (← mkPickGoal pos))
  return (acc.push step.tactic, tacticState)

end LazyStep

namespace UScript

def render (s : UScript) (rootGoal : MVarId) :
    MetaM (Array (TSyntax `tactic)) := do
  let mut script := Array.mkEmpty s.size
  let mut tacticState : TacticState := { goals := #[rootGoal] }
  for step in s do
    let (script', tacticState') ← step.render script tacticState
    script := script'
    tacticState := tacticState'
  return script

def renderTacticSeq (s : UScript) (rootGoal : MVarId) :
    MetaM (TSyntax ``tacticSeq) := do
  `(tacticSeq| $(← s.render rootGoal):tactic*)

end UScript

def addTryThisTacticSeqSuggestion (ref : Syntax)
    (tacs : Array (TSyntax `tactic)) : MetaM Unit := do
  /- Render one tactic per line, indented to the column of `iaesop?` (i.e. the
  surrounding tactic-block level). Building the text ourselves avoids the extra
  indentation level that a `tacticSeq` adds, which would otherwise push the
  inserted proof one tab too deep. -/
  let map ← getFileMap
  let col := match ref.getPos? with
    | some pos => (map.toPosition pos).column
    | none => 0
  let width := Lean.Meta.Tactic.TryThis.getInputWidth (← getOptions)
  let lineStrs ← tacs.mapM fun t => do
    let fmt ← PrettyPrinter.ppTactic t
    pure <| fmt.pretty (width := width) (indent := col) (column := col)
  let pad := "\n".pushn ' ' col
  let msgText := String.intercalate pad lineStrs.toList
  let suggestion : Lean.Meta.Tactic.TryThis.Suggestion := {
    suggestion := .string msgText
    toCodeActionTitle? := some λ _ => "Replace iaesop? with the proof it found"
    messageData? := some msgText
  }
  Lean.Meta.Tactic.TryThis.addSuggestion ref suggestion (header := "Try this:\n")

end Script
