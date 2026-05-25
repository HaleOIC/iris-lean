module

public meta import Iris.ProofMode.Aesop.Rule.Commit.Basic
public meta import Iris.ProofMode.Tactics.Assumption
public meta import Iris.ProofMode.Tactics.HaveCore

public meta section

namespace Iris.ProofMode.Aesop.Rule.ApplyHyps

open Lean Meta Qq Std
open Iris.BI
open Iris.ProofMode

variable {Q : Type} [Queue Q]

/- Record information produced during expansion -/
private structure ApplyHypExpansion where
  usedHyp : AppliedHyp
  goals : Array SubGoal
  fullContextIrisSubgoals : Array IrisGoal
  postState : SavedState

/- Make a close-goal expansion when the selected hypothesis directly proves the target. -/
private def mkCloseGoalExpansion?
    {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)}
    (usedHyp : AppliedHyp) (p : Q(Bool))
    (hypType target : Q($prop)) :
    MetaM (Option ApplyHypExpansion) := do
  let hypType : Q($prop) ← instantiateMVars hypType
  let target : Q($prop) ← instantiateMVars target
  let preState ← saveState
  /- Search only checks that the hypothesis matches the target;
  affine/absorbing side conditions are checked when the proof is assigned. -/
  match ← ProofMode.trySynthInstanceQ q(FromAssumption $p .in $hypType $target) with
  | .none | .undef => preState.restore; return none
  | .some _ => return some {
      usedHyp, goals := #[], fullContextIrisSubgoals := #[], postState := ← saveState
    }

/- Collect premises produced by applying a hypothesis to the target. -/
private partial def collectApplyPremises?
    {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)}
    (p : Q(Bool)) (hypType target : Q($prop)) :
    MetaM (Option (Array Q($prop))) := do
  let hypType : Q($prop) ← instantiateMVars hypType
  let target : Q($prop) ← instantiateMVars target
  let premise ← mkFreshExprMVarQ prop
  let preState ← saveState

  /- Base case: one premise is enough to make the hypothesis prove the target. -/
  match ← ProofMode.trySynthInstanceQ q(IntoWand $p false $hypType .out $premise .in $target) with
  | .some _ => return some #[premise]
  | .none | .undef => preState.restore

  /- Recursive case: peel one premise, then keep applying the remaining wand. -/
  let restTarget ← mkFreshExprMVarQ prop
  match ← ProofMode.trySynthInstanceQ q(IntoWand $p false $hypType .out $premise .out $restTarget) with
  | .none | .undef => preState.restore; return none
  | .some _ => match ← collectApplyPremises? (bi := bi) q(false) restTarget target with
    | some premises => return some (#[premise] ++ premises)
    | none => preState.restore; return none

/- Turn each collected premise into both a search subgoal and its IrisGoal template. -/
private def mkChildren (irisGoal : IrisGoal) (tag : Name)
    {e' : Q($irisGoal.prop)} (hyps' : Hyps irisGoal.bi e')
    (premises : Array Q($irisGoal.prop)) :
    MetaM (Array SubGoal × Array IrisGoal) := do
  premises.foldlM (init := (#[], #[])) λ (goals, irisSubgoals) premise => do
    let premise : Q($irisGoal.prop) ← instantiateMVars premise
    let childIrisGoal := { irisGoal with e := e', hyps := hyps', goal := premise }
    let goalExpr ← mkFreshExprSyntheticOpaqueMVar (IrisGoal.toExpr childIrisGoal) tag
    let goal := goalExpr.mvarId!
    return (
      goals.push { goal, addedFVars := {}, removedFVars := {} },
      irisSubgoals.push childIrisGoal
    )

/- Collect close-goal and apply expansions from Iris local hypotheses. -/
private partial def collectFromIris
    {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)}
    (irisGoal : IrisGoal) (tag : Name) (baseState : SavedState) :
    ∀ {e}, Hyps bi e →
      MetaM (Array ApplyHypExpansion × Array ApplyHypExpansion)
  | _, .emp _ => return (#[], #[])
  | _, .sep _ _ _ _ lhs rhs => do
    let (lhsClose, lhsApply) ← collectFromIris irisGoal tag baseState lhs
    let (rhsClose, rhsApply) ← collectFromIris irisGoal tag baseState rhs
    return (lhsClose ++ rhsClose, lhsApply ++ rhsApply)
  | _, .hyp _ name ivar p ty _ => do
    baseState.restore
    /- `p` marks whether this Iris hypothesis lives in the intuitionistic context. -/
    let usedHyp : AppliedHyp :=
      if isTrue p then .intuitionistic { name, ivar } else .spatial { name, ivar }
    let closeExpansion? ←
      mkCloseGoalExpansion? (bi := bi) usedHyp p ty irisGoal.goal

    baseState.restore
    let mut applyExpansions := #[]
    if let some premises ← collectApplyPremises? (bi := bi) p ty irisGoal.goal then
      let some ⟨_, _, hyps', _, _, _, _, _⟩ ←
          irisGoal.hyps.removeG false λ _ ivar' _ _ => do
            if ivar == ivar' then return some ()
            else return none
        | throwError "iaesop: applyHyps candidate disappear from Hyps"
      let (goals, fullContextIrisSubgoals) ←
        mkChildren irisGoal tag hyps' premises
      applyExpansions := applyExpansions.push {
        usedHyp, goals, fullContextIrisSubgoals, postState := ← saveState
      }

    baseState.restore
    return (closeExpansion?.toArray, applyExpansions)

/- Collect close-goal and apply expansions from Lean local hypotheses. -/
private def collectFromLean (irisGoal : IrisGoal) (tag : Name)
    (baseState : SavedState) : MetaM (Array ApplyHypExpansion) := do
  let { prop, bi, goal := target, .. } := irisGoal
  baseState.restore

  /- Try each usable local declaration independently from the same base state. -/
  let mut closeExpansions := #[]
  let mut applyExpansions := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then
      continue
    baseState.restore

    /- Peel explicit and implicit forall binders to expose the proposition being proved. -/
    let ⟨_, _, ty⟩ ← forallMetaTelescope (← instantiateMVars decl.type)
    if ! (← Meta.isProp ty) then continue
    have ty : Q(Prop) := ty

    /- Bridge the Lean proposition into the current Iris BI before probing close/apply paths. -/
    let hyp ← mkFreshExprMVarQ prop
    match ← ProofMode.trySynthInstanceQ q(AsEmpValid .into $ty .in $prop .in $bi $hyp) with
    | .none | .undef => continue
    | .some _ =>
      let bridgedState ← saveState
      let usedHyp := AppliedHyp.lean decl.userName decl.fvarId
      if let some expansion ←
          mkCloseGoalExpansion? (bi := bi) usedHyp q(true) hyp target then
        closeExpansions := closeExpansions.push expansion
      bridgedState.restore

      let some premises ← collectApplyPremises? (bi := bi) q(true) hyp target
        | continue
      let (goals, fullContextIrisSubgoals) ←
        mkChildren irisGoal tag irisGoal.hyps premises
      applyExpansions := applyExpansions.push {
        usedHyp, goals, fullContextIrisSubgoals, postState := ← saveState
      }
  baseState.restore
  return closeExpansions ++ applyExpansions

/- Search stage work -/
def run (input : RuleInput) : SearchM Q RuleOutput := do
  /- Collect possible hypothesis that can be applied in current goal -/
  let goal := input.goal
  let expansions ← liftM do
    restoreState input.state
    goal.withContext do
      let goalType ← instantiateMVars (← goal.getType)
      let some irisGoal := parseIrisGoal? goalType
        | throwError "iaesop: applyHyps rule search must work in iris proof-mode context"
      let tag ← goal.getTag
      let baseState ← saveState
      let (irisCloseExpansions, irisApplyExpansions) ←
        collectFromIris irisGoal tag baseState irisGoal.hyps
      let leanExpansions ←
        collectFromLean irisGoal tag baseState
      return irisCloseExpansions ++ irisApplyExpansions ++ leanExpansions
  if expansions.isEmpty then return {}

  /- Construct corresponding Rapp specs for each probed hypothesis -/
  let specs ← expansions.mapM λ expansion => do
    let usedHypName :=
      match expansion.usedHyp with
      | .spatial hyp | .intuitionistic hyp => hyp.name
      | .lean userName .. => userName
    dbg_trace s!"applyHyps selected {usedHypName} and generated {expansion.goals.size} goals"
    for irisGoal in expansion.fullContextIrisSubgoals do
      let targetFmt ← liftM <| ppExpr irisGoal.goal
      dbg_trace s!"  applyHyps child target: {targetFmt.pretty}"
    return {
      goals := expansion.goals
      postState := expansion.postState
      successPossibility := .hundred
      effect :=
        match expansion.goals.size with
        | 0 => some (.closeGoal (some expansion.usedHyp))
        | 1 => none
        | _ =>
          some (.contextManagement
            expansion.fullContextIrisSubgoals (some expansion.usedHyp))
    }
  return RuleOutput.ofRappSpecs specs

def replay (input : RuleReplayInput) : ProofModeM (Array MVarId) := do
  return #[input.goal]

end Iris.ProofMode.Aesop.Rule.ApplyHyps
