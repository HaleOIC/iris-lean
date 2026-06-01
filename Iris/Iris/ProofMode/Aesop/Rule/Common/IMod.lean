module

public meta import Iris.ProofMode.Aesop.Rule.Commit.Basic
public meta import Iris.ProofMode.Aesop.Search.Names
public meta import Iris.ProofMode.Tactics.Cases

public meta section

namespace Iris.ProofMode.Aesop.Rule.IMod

open Lean Meta Qq Std
open Iris.ProofMode

variable {Q : Type} [Queue Q]

/- Collect `imod` expansions from Iris local hypotheses. -/
private partial def collectFromIris
    (goal : MVarId) (irisGoal : IrisGoal) (baseState : SavedState)
    (depth : Nat) :
    ∀ {e}, Hyps irisGoal.bi e → ProofModeM (Array RappSpec)
  | _, .emp _ => return #[]
  | _, .sep _ _ _ _ lhs rhs => do
    return (← collectFromIris goal irisGoal baseState depth lhs) ++
      (← collectFromIris goal irisGoal baseState depth rhs)
  | _, .hyp _ name ivar _ _ _ => do
    baseState.restore

    /- Remove the candidate hypothesis from the Iris context before probing `imod`.
       We pass `rp := true` so that an intuitionistic hypothesis is *consumed* rather than
       duplicated: `imod` transforms `□?p A` into the eliminated `□?p' A'`, exactly as the
       interactive `imod` tactic does (`Hyps.remove (!keep)`). Keeping the original copy would
       leave e.g. `◇ □ P` in context after eliminating its `◇`, making `imod` reapplicable
       forever and sending the search into an infinite loop. -/
    let some ⟨_, e', hyps', out, ty, p, _, _⟩ ←
        irisGoal.hyps.removeG true λ _ ivar' _ _ => do
          if ivar == ivar' then return some ()
          else return none
      | return #[]
    have : $out =Q iprop(□?$p $ty) := ⟨⟩

    /- Generate a fresh binder name for the hypothesis produced by modal elimination. -/
    let pat ← mkFreshBinderFromNames (hypNameArray irisGoal.hyps) depth
    let (patName, _) ← getFreshName pat
    let childRef ← IO.mkRef (none : Option (SubGoal × IrisGoal))
    try let _ ←
      iModCore irisGoal.bi e' irisGoal.goal p ty λ p' ty' goal' =>
        iCasesCore irisGoal.bi hyps' goal' (.one pat) p' ty' λ hyps goal' => do
          let childExpr ← mkBIGoal hyps goal' (← goal.getTag)
          let childGoal := childExpr.mvarId!
          let childIrisGoal ← childGoal.withContext do
            let childType ← instantiateMVars (← childGoal.getType)
            let some childIrisGoal := parseIrisGoal? childType
              | throwError "iaesop: imod generated a non-Iris child goal"
            return childIrisGoal
          childRef.set (some (
            { goal := childGoal, addedFVars := {}, removedFVars := {} },
            childIrisGoal
          ))
          return childExpr
    catch _ =>
      baseState.restore
      return #[]

    /- Read the fabricated child goal and package it as a rule application. -/
    let some (child, childIrisGoal) := ← childRef.get
      | throwError "iaesop: imod did not generate a child goal"
    let usedHyp : AppliedHyp :=
      let hyp := { name, ivar }
      if isTrue p then .intuitionistic hyp else .spatial hyp
    let postState ← liftM (m := MetaM) saveState
    let generatedHyp? :=
      match childIrisGoal.hyps.find? patName with
      | some (ivar, p, _) =>
        if isTrue p then none else some { name := patName, ivar }
      | none => none

    dbg_trace s!"imod selected {name} and generated 1 goal"
    let targetFmt ← liftM <| child.goal.withContext <| ppExpr childIrisGoal.goal
    dbg_trace s!"  imod child target: {targetFmt.pretty}"
    return #[{
      goals := #[child],
      postState
      successPossibility := .hundred
      effect := { generatedSpatialHyp? := generatedHyp?, usedHyp? := some usedHyp, action := none }
    }]

/- Search for `imod` applications among current Iris hypotheses. -/
def run (input : RuleInput) : SearchM Q RuleOutput := do
  let goal := input.goal
  let specs ← liftM (m := ProofModeM) do
    input.state.restore
    goal.withContext do
      let goalType ← instantiateMVars (← goal.getType)
      let some irisGoal := parseIrisGoal? goalType
        | throwError "iaesop: imod rule search must work in iris proof-mode context"
      let baseState ← liftM (m := MetaM) saveState
      collectFromIris input.goal irisGoal baseState input.depth irisGoal.hyps
  return RuleOutput.ofRappSpecs specs

/- [Note] Make sure you are in the correct context -/
def replay (input : RuleReplayInput) : ProofModeM (Array MVarId) := do
  let some usedHyp := input.rapp.usedHyp?
    | throwError "iaesop(baseline): imod replay is missing the selected hypothesis"
  input.goal.withContext do
    let goalType ← instantiateMVars (← input.goal.getType)
    let some irisGoal := parseIrisGoal? goalType
      | throwError "iaesop(baseline): imod replay expected an Iris goal"
    let some ⟨_, e', hyps', out, ty, p, _, removePf⟩ ←
        irisGoal.hyps.removeG true fun name _ p _ => do
          match usedHyp with
          | .spatial hyp =>
            if hyp.name == name && !isTrue p then return some () else return none
          | .intuitionistic hyp =>
            if hyp.name == name && isTrue p then return some () else return none
          | .lean .. => return none
      | throwError "iaesop(baseline): imod replay selected hypothesis disappeared"
    have : $out =Q iprop(□?$p $ty) := ⟨⟩
    let parent ← input.rapp.parent.get
    let pat ← mkFreshBinderFromNames (hypNameArray irisGoal.hyps) parent.depth
    let childRef ← IO.mkRef (none : Option MVarId)
    let proof ←
      iModCore irisGoal.bi e' irisGoal.goal p ty fun p' ty' goal' =>
        iCasesCore irisGoal.bi hyps' goal' (.one pat) p' ty' fun hyps goal' => do
          let childExpr ← mkBIGoal hyps goal' (← input.goal.getTag)
          childRef.set (some childExpr.mvarId!)
          return childExpr
    input.goal.assign q(($removePf).1.trans $proof)
    let some childGoal := ← childRef.get
      | throwError "iaesop(baseline): imod replay did not generate a child goal"
    return #[childGoal]

end Iris.ProofMode.Aesop.Rule.IMod
