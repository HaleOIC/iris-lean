module

public meta import Iris.ProofMode.Aesop.Rule.Commit.Basic
public meta import Iris.ProofMode.Aesop.Search.Names
public meta import Iris.ProofMode.Tactics.HaveCore

public meta section

namespace Iris.ProofMode.Aesop.Rule.HaveHyps

open Lean Meta Qq Std Iris BI ProofMode

variable {Q : Type} [Queue Q]

/- Record information produced during expansion -/
private structure HaveHypsExpansion where
  usedHyp : AppliedHyp
  generatedHyp? : Option IrisHyp
  goals : Array SubGoal
  fullContextIrisSubgoals : Array IrisGoal
  postState : SavedState

/- Collect premises and conclusion from one hypothesis -/
private partial def parseHypothesis? {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)}
    (p : Q(Bool)) (hyp : Q($prop)) : MetaM (Option (Array Q($prop) × Q($prop))) := do
  let hyp : Q($prop) ← instantiateMVars hyp
  let premise ← mkFreshExprMVarQ prop
  let rest ← mkFreshExprMVarQ prop
  let preState ← saveState
  match ← trySynthInstanceProbeQ q(IntoWand $p false $hyp .out $premise .out $rest) with
  | .none | .undef => preState.restore; return none
  | .some _ =>
    let premise : Q($prop) ← instantiateMVars premise
    let rest : Q($prop) ← instantiateMVars rest
    match ← parseHypothesis? (bi := bi) q(false) rest with
    | some (premises, conclusion) =>
      return some (#[premise] ++ premises, conclusion)
    | none =>
      return some (#[premise], rest)

/- Check whether the derived conclusion exposes structure useful for forward search:
   existential, separating-conjunctive, disjunctive, modal, or except-0 structure. -/
private def satisfy? {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)}
    (hyp : Q($prop)) : MetaM Bool := do
  let hyp : Q($prop) ← instantiateMVars hyp
  let preState ← saveState
  let v ← mkFreshLevelMVar
  let α : Q(Sort v) ← mkFreshExprMVarQ q(Sort v)
  let Φ : Q($α → $prop) ← mkFreshExprMVarQ q($α → $prop)
  match ← trySynthInstanceProbeQ q(IntoExists $hyp $Φ) with
  | .some _ => preState.restore; return true
  | .none | .undef => preState.restore

  let left ← mkFreshExprMVarQ prop
  let right ← mkFreshExprMVarQ prop
  match ← trySynthInstanceProbeQ q(IntoSep $hyp $left $right) with
  | .some _ => preState.restore; return true
  | .none | .undef => preState.restore

  let left ← mkFreshExprMVarQ prop
  let right ← mkFreshExprMVarQ prop
  match ← trySynthInstanceProbeQ q(IntoOr $hyp $left $right) with
  | .some _ => preState.restore; return true
  | .none | .undef => preState.restore

  let Φ ← mkFreshExprMVarQ q(Prop)
  let M ← mkFreshExprMVarQ q(Modality $prop $prop)
  let sel ← mkFreshExprMVarQ prop
  let inner ← mkFreshExprMVarQ prop
  match ← trySynthInstanceProbeQ q(@FromModal $prop $prop $bi $bi $Φ $M $sel $hyp $inner) with
  | .some _ => preState.restore; return true
  | .none | .undef => preState.restore

  let inner ← mkFreshExprMVarQ prop
  match ← trySynthInstanceProbeQ q(IntoExcept0 $hyp $inner) with
  | .some _ => preState.restore; return true
  | .none | .undef => preState.restore; return false

/- Turn each collected premise and conclusion into both a search subgoal and its IrisGoal template. -/
private def mkChildren (irisGoal : IrisGoal) (tag : Name) (depth : Nat)
    {e' : Q($irisGoal.prop)} (hyps' : Hyps irisGoal.bi e')
    (premises : Array Q($irisGoal.prop)) (conclusion : Q($irisGoal.prop)):
    ProofModeM (Array SubGoal × Array IrisGoal × Option IrisHyp) := do
  let (goals, irisSubgoals) ← premises.foldlM (init := (#[], #[])) λ (goals, irisSubgoals) premise => do
    let premise : Q($irisGoal.prop) ← instantiateMVars premise
    let childIrisGoal := { irisGoal with e := e', hyps := hyps', goal := premise }
    let goalExpr ← mkBIGoal childIrisGoal.hyps childIrisGoal.goal tag
    let goal := goalExpr.mvarId!
    return (
      goals.push { goal, addedFVars := {}, removedFVars := {} },
      irisSubgoals.push childIrisGoal
    )

  let conclusion : Q($irisGoal.prop) ← instantiateMVars conclusion
  let binder ← mkFreshBinderFromNames (hypNameArray irisGoal.hyps) depth
  let (name, _) ← getFreshName binder
  let ivar ← mkFreshIVarId false
  let hypsWithConclusion := Hyps.add irisGoal.bi name ivar q(false) conclusion hyps'
  let childIrisGoal := { irisGoal with e := _, hyps := hypsWithConclusion, goal := irisGoal.goal }
  let goalExpr ← mkBIGoal childIrisGoal.hyps childIrisGoal.goal tag
  let goal := goalExpr.mvarId!
  let goals := goals.push { goal, addedFVars := {}, removedFVars := {} }
  let irisSubgoals := irisSubgoals.push childIrisGoal
  let generatedHyp? := if ivar.persistent? then none else some { name, ivar }
  return (goals, irisSubgoals, generatedHyp?)

/- Collect have expansions from Iris local hypotheses -/
private def collectFromIris {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)}
    (irisGoal : IrisGoal) (tag : Name) (depth : Nat) (baseState : SavedState) :
    ∀ {e}, Hyps bi e → ProofModeM (Array HaveHypsExpansion)
  | _, .emp _ => return #[]
  | _, .sep _ _ _ _ lhs rhs => do
    return (← collectFromIris irisGoal tag depth baseState lhs) ++
      (← collectFromIris irisGoal tag depth baseState rhs)
  | _, .hyp _ name ivar p ty _ => do
    baseState.restore
    /- Check whether conclusion satisfy the forward requirement (otherwise explosion) -/
    let mut haveExpansions := #[]
    if let some (premises, conclusion) ← parseHypothesis? (bi := bi) p ty then
      if !premises.isEmpty && (← satisfy? (bi := bi) conclusion) then
        let usedHyp : AppliedHyp :=
          if isTrue p then .intuitionistic { name, ivar } else .spatial { name, ivar }
        let some ⟨_, _, hyps', _, _, _, _, _⟩ ←
          irisGoal.hyps.removeG false λ _ ivar' _ _ => do
            if ivar == ivar' then return some ()
            else return none
        | throwError "iaesop: haveHyps candidate disappear from Hyps"
        let (goals, fullContextIrisSubgoals, generatedHyp?) ←
          mkChildren irisGoal tag depth hyps' premises conclusion
        haveExpansions := haveExpansions.push {
          usedHyp, generatedHyp?, goals, fullContextIrisSubgoals,
          postState := ← liftM (m := MetaM) saveState
        }
    baseState.restore
    return haveExpansions

/- Search stage work -/
def run (input : RuleInput) : SearchM Q RuleOutput := do
  let goal := input.goal
  let expansions ← liftM (m := ProofModeM) do
    input.state.restore
    goal.withContext do
      let goalType ← instantiateMVars (← goal.getType)
      let some irisGoal := parseIrisGoal? goalType
        | throwError "iaesop : haveHyps rule search must work in iris proof-mode context"
      let tag ← goal.getTag
      let baseState ← liftM (m := MetaM) saveState
      let irisHaveExpansions ← collectFromIris irisGoal tag input.depth baseState irisGoal.hyps
      return irisHaveExpansions
  if expansions.isEmpty then
    return {}

  /- Construct corresponding Rapp specs for each probed hypothesis -/
  let specs ← expansions.mapM λ expansion => do
    let usedHypName :=
      match expansion.usedHyp with
      | .spatial hyp | .intuitionistic hyp => hyp.name
      | .lean userName .. => userName
    trace[iaesop.tactic] s!"haveHyps selected {usedHypName} and generated {expansion.goals.size} goals"
    for irisGoal in expansion.fullContextIrisSubgoals do
      let targetFmt ← liftM <| ppExpr irisGoal.goal
      trace[iaesop.tactic] s!"  haveHyps child target: {targetFmt.pretty}"
    return {
      goals := expansion.goals
      postState := expansion.postState
      successPossibility := ⟨0.45⟩
      effect := {
        usedHyps := #[expansion.usedHyp]
        generatedSpatialHyps := expansion.generatedHyp?.toArray
        action := some (.manageContext expansion.fullContextIrisSubgoals)
      }
    }
  return RuleOutput.ofRappSpecs specs

/- Helper function for removing the replayed Iris hypothesis from `Hyps`. -/
private def irisHypMatches (usedHyp : AppliedHyp)
    (name : Name) (p : Q(Bool)) : Bool :=
  match usedHyp with
  | .spatial hyp => hyp.name == name && !isTrue p
  | .intuitionistic hyp => hyp.name == name && isTrue p
  | .lean .. => false

/- Replay the premise subgoals and return the conclusion produced by the selected hypothesis. -/
private partial def replayHaveCore
    {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)} {e : Q($prop)}
    (hyps : Hyps bi e) (p : Q(Bool)) (hypType : Q($prop))
    (contexts : Array (Array IrisHyp)) (tag : Name) :
    ProofModeM ((e' : Q($prop)) × Hyps bi e' × (conclusion : Q($prop)) ×
      Q($e ∗ □?$p $hypType ⊢ $e' ∗ $conclusion) × Array MVarId) := do
  let premise ← mkFreshExprMVarQ prop
  let rest ← mkFreshExprMVarQ prop
  let some inst ← ProofModeM.trySynthInstanceQ
      q(IntoWand $p false $hypType .out $premise .out $rest)
    | throwError "iaesop(baseline): haveHyps replay selected hypothesis has too few premises"
  let premise : Q($prop) ← instantiateMVars premise
  let rest : Q($prop) ← instantiateMVars rest
  let some firstContext := contexts[0]?
    | throwError "iaesop(baseline): haveHyps replay is missing the first premise context"
  let premiseNames := firstContext.map (·.name)
  let ⟨eRemaining, _, remainingHyps, premiseHyps, splitPf⟩ :=
    hyps.split bi λ name _ => premiseNames.contains name
  let premiseProof ← mkBIGoal premiseHyps premise tag
  let inst : Q(IntoWand $p false $hypType .out $premise .out $rest) := inst
  let step : Q($e ∗ □?$p $hypType ⊢ $eRemaining ∗ $rest) :=
    q(specialize_wand_subgoal
      (Q := $hypType) (P1 := $premise)
      (inst := $inst)
      $rest (.rfl) $splitPf $premiseProof)
  if contexts.size == 1 then
    return ⟨eRemaining, remainingHyps, rest, step, #[premiseProof.mvarId!]⟩
  let ⟨eFinal, finalHyps, conclusion, restProof, restGoals⟩ ←
    replayHaveCore remainingHyps q(false) rest (contexts.extract 1 contexts.size) tag
  return ⟨eFinal, finalHyps, conclusion,
    q(Entails.trans $step $restProof), #[premiseProof.mvarId!] ++ restGoals⟩

/- Replay `have` generated from an Iris hypothesis. -/
private def replayHave (goalMVarId : MVarId) (usedHyp : AppliedHyp)
    (contexts : Array (Array IrisHyp)) (depth : Nat) :
    ProofModeM (Array MVarId) := do
  goalMVarId.withContext do
    let goalType ← instantiateMVars (← goalMVarId.getType)
    let some { bi, hyps, goal := target, .. } := parseIrisGoal? goalType
      | throwError "iaesop(baseline): haveHyps replay expected an Iris goal"
    let tag ← goalMVarId.getTag
    match usedHyp with
    | .spatial _ | .intuitionistic _ =>
      let some ⟨_, _, hyps', out, hypType, p, _, removePf⟩ ←
          hyps.removeG false λ name _ p _ => do
            if irisHypMatches usedHyp name p then return some ()
            else return none
        | throwError "iaesop(baseline): haveHyps replay selected Iris hypothesis disappeared"
      have : $out =Q iprop(□?$p $hypType) := ⟨⟩
      let ⟨_, remainingHyps, conclusion, haveProof, premiseGoals⟩ ←
        replayHaveCore (bi := bi) hyps' p hypType contexts tag
      let binder ← mkFreshBinderFromNames (hypNameArray hyps) depth
      let (name, _) ← getFreshName binder
      let ivar ← mkFreshIVarId false
      let finalHyps := Hyps.add bi name ivar q(false) conclusion remainingHyps
      let finalProof ← mkBIGoal finalHyps target tag
      goalMVarId.assign q(($removePf).1.trans (Entails.trans $haveProof $finalProof))
      return premiseGoals.push finalProof.mvarId!
    | .lean .. =>
      throwError "iaesop(baseline): haveHyps replay only supports Iris hypotheses"

def replay (input : RuleReplayInput) : ProofModeM (Array MVarId) := do
  let some usedHyp := input.rapp.usedHyp?
    | throwError "iaesop(baseline): haveHyps replay is missing the selected hypothesis"
  let obun ← input.rapp.children.get
  if !obun.kind.isManaged then
    throwError "iaesop(baseline): haveHyps replay expected a managed child bundle"
  if obun.goals.size < 2 then
    throwError "iaesop(baseline): haveHyps replay expected at least one premise and one continuation goal"
  if obun.finalizedSpatialSplits.size != obun.goals.size then
    throwError s!"iaesop(baseline): haveHyps replay found {obun.finalizedSpatialSplits.size} finalized spatial splits for {obun.goals.size} generated goals"
  let parent ← input.rapp.parent.get
  replayHave input.goal usedHyp
    (obun.finalizedSpatialSplits.extract 0 (obun.goals.size - 1)) parent.depth

end Iris.ProofMode.Aesop.Rule.HaveHyps
