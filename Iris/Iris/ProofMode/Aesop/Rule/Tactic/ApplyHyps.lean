module

public meta import Iris.ProofMode.Aesop.Rule.Commit.Basic
public meta import Iris.ProofMode.Aesop.Rule.Backward.Shape
public meta import Iris.ProofMode.Tactics.Apply
public meta import Iris.ProofMode.Tactics.Assumption
public meta import Iris.ProofMode.Tactics.HaveCore

public meta section

namespace Iris.ProofMode.Aesop.Rule.ApplyHyps

open Lean Meta Qq Std
open Iris.BI
open Iris.ProofMode

variable {Q : Type} [Queue Q]

/- Extract a cheaply comparable conclusion from the common hypothesis shapes.
Unknown connectives deliberately return `none`, preserving the complete
typeclass-driven fallback for modalities and user-defined instances. -/
private partial def candidateConclusion? (type : Expr) : MetaM (Option Expr) := do
  let type ← instantiateMVars type
  let type := type.consumeMData
  if let some args := type.appM? ``BIBase.wand then
    let some target := args.back? | return none
    candidateConclusion? target
  else if let some args := type.appM? ``BIBase.imp then
    let some target := args.back? | return none
    candidateConclusion? target
  else if let some args := type.appM? ``BIBase.intuitionistically then
    let some target := args.back? | return none
    candidateConclusion? target
  else if let some args := type.appM? ``BIBase.affinely then
    let some target := args.back? | return none
    candidateConclusion? target
  else if let some args := type.appM? ``BIBase.persistently then
    let some target := args.back? | return none
    candidateConclusion? target
  else if type.isAppOfArity ``BIBase.and 4 || type.isAppOfArity ``BIBase.or 4 ||
      type.isAppOfArity ``BIBase.sep 4 || type.isAppOf ``BIBase.later ||
      type.isAppOf ``BIBase.forall || type.isAppOf ``BIBase.exists then
    return none
  else
    return some type

private def conclusionMatches? (conclusion target : Expr) : MetaM Bool := do
  let conclusionMVars ← getMVars conclusion
  let targetMVars ← getMVars target
  if !conclusionMVars.isEmpty || !targetMVars.isEmpty then return true
  withoutModifyingState do
    try isDefEq conclusion target
    catch _ => return false

private def irisCandidateCouldMatch (type target : Expr) : MetaM Bool := do
  let some conclusion ← candidateConclusion? type | return true
  conclusionMatches? conclusion target

private def leanCandidateCouldMatch (type target : Expr) : MetaM Bool := do
  let type := type.consumeMData
  let target? :=
    (type.appM? ``BIBase.Entails <|> type.appM? ``BIBase.EmpValid <|>
      type.appM? ``BIBase.BiEntails).bind Array.back?
  let some candidateTarget := target? | return true
  let some conclusion ← candidateConclusion? candidateTarget | return true
  conclusionMatches? conclusion target

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
  match ← trySynthInstanceProbeQ q(FromAssumption $p .in $hypType $target) with
  | .none | .undef => preState.restore; return none
  | .some _ =>
    let _ := ← instantiateMVars hypType
    let _ := ← instantiateMVars target
    return some {
      usedHyp, goals := #[], fullContextIrisSubgoals := #[], postState := ← saveState
    }

/- Collect premises produced by applying a hypothesis to the target. -/
partial def collectApplyPremises?
    {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)}
    (p : Q(Bool)) (hypType target : Q($prop)) :
    MetaM (Option (Array Q($prop))) := do
  let hypType : Q($prop) ← instantiateMVars hypType
  let target : Q($prop) ← instantiateMVars target
  let premise ← mkFreshExprMVarQ prop
  let preState ← saveState

  /- Base case: one premise is enough to make the hypothesis prove the target. -/
  match ← trySynthInstanceProbeQ q(IntoWand $p false $hypType .out $premise .in $target) with
  | .some _ =>
    let premise : Q($prop) ← instantiateMVars premise
    return some #[premise]
  | .none | .undef => preState.restore

  /- Recursive case: peel one premise, then keep applying the remaining wand. -/
  let restTarget ← mkFreshExprMVarQ prop
  match ← trySynthInstanceProbeQ q(IntoWand $p false $hypType .out $premise .out $restTarget) with
  | .none | .undef => preState.restore; return none
  | .some _ =>
    let premise : Q($prop) ← instantiateMVars premise
    let restTarget : Q($prop) ← instantiateMVars restTarget
    match ← collectApplyPremises? (bi := bi) q(false) restTarget target with
    | some premises =>
      let premises : Array Q(«$prop») ← premises.mapM λ premise => do
         instantiateMVars premise
      return some (#[premise] ++ premises)
    | none => preState.restore; return none

/- Turn each collected premise into both a search subgoal and its IrisGoal template. -/
def mkChildren (irisGoal : IrisGoal) (tag : Name)
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
    unless ← irisCandidateCouldMatch ty irisGoal.goal do
      trace[iaesop.tactic] "applyHyps prefilter skipped Iris hypothesis {name}"
      return (#[], #[])
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
    let ty ← instantiateMVars (← instantiateMVars decl.type)
    if ! (← Meta.isProp ty) then continue
    have ty : Q(Prop) := ty
    unless ← leanCandidateCouldMatch ty target do
      trace[iaesop.tactic] "applyHyps prefilter skipped Lean hypothesis {decl.userName}"
      continue

    /- Bridge the Lean proposition into the current Iris BI before probing close/apply paths. -/
    let hyp ← mkFreshExprMVarQ prop
    match ← trySynthInstanceProbeQ q(AsEmpValid .into $ty .in $prop .in $bi $hyp) with
    | .none | .undef => continue
    | .some _ =>
      let hyp : Q($prop) ← instantiateMVars hyp
      let _ := ← instantiateMVars ty
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
def run (input : RuleInput) : CoreM Q RuleOutput := do
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
    let successPossibility : Percent :=
      match expansion.usedHyp with
      | .lean .. => ⟨0.55⟩
      | .intuitionistic .. => ⟨0.7⟩
      | .spatial .. => ⟨0.85⟩
    trace[iaesop.tactic] s!"applyHyps selected {usedHypName} and generated {expansion.goals.size} goals"
    for irisGoal in expansion.fullContextIrisSubgoals do
      let targetFmt ← liftM <| ppExpr irisGoal.goal
      trace[iaesop.tactic] s!"  applyHyps child target: {targetFmt.pretty}"
    return {
      goals := expansion.goals
      postState := expansion.postState
      successPossibility
      effect := {
        usedHyps := #[expansion.usedHyp]
        action :=
          if expansion.goals.isEmpty then some .closeGoal
          else if expansion.goals.size == 1 then none
          else some (.manageContext expansion.fullContextIrisSubgoals)
      }
    }
  return RuleOutput.ofRappSpecs specs

/- Helper function for removing spatial hyp from Hyps -/
private def irisHypMatches (usedHyp : AppliedHyp)
    (name : Name) (p : Q(Bool)) : Bool :=
  match usedHyp with
  | .spatial hyp => hyp.name == name && !isTrue p
  | .intuitionistic hyp => hyp.name == name && isTrue p
  | .lean .. => false

/- Transform Lean hypothesis into Iris proof-mode as an applicable one -/
private def mkLeanHypProof
    {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)} {e : Q($prop)}
    (userName : Name) (fvarId : FVarId) :
    ProofModeM ((hyp : Q($prop)) × Q($e ⊢ $e ∗ □ $hyp)) := do
  /- Find the replayed Lean hypothesis and instantiate any forall binders. -/
  let some decl := ← (← getLCtx).findDeclM? λ decl => do
    pure $ if decl.isImplementationDetail then none
    else if decl.fvarId == fvarId || decl.userName == userName then some decl
    else none
  | throwError s!"iaesop(baseline): applyHyps replay could not find Lean hypothesis {userName}"
  let val := mkFVar decl.fvarId
  let ty : Q(Prop) ← instantiateMVars (← instantiateMVars decl.type)
  let hyp ← mkFreshExprMVarQ prop
  let some inst ← ProofModeM.trySynthInstanceQ
      q(AsEmpValid .into $ty .in $prop .in $bi $hyp)
    | throwError s!"iaesop(baseline): applyHyps replay cannot bridge Lean hypothesis {userName} into Iris"
  let hyp : Q($prop) ← instantiateMVars hyp
  let ty : Q(Prop) ← instantiateMVars ty
  let val : Q($ty) ← instantiateMVars val
  let inst : Q(AsEmpValid .into $ty .in $prop .in $bi $hyp) := inst
  return ⟨hyp, q(have_asEmpValid (P := $hyp) (Q := $e) (h1 := $inst) $val)⟩

/- Construct a close proof by using given hypothesis -/
def mkCloseCoreProof
    {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)} {e : Q($prop)}
    (p : Q(Bool)) (hypType target : Q($prop)) :
    ProofModeM Q($e ∗ □?$p $hypType ⊢ $target) := do
  let some inst ← ProofModeM.trySynthInstanceQ q(FromAssumption $p .in $hypType $target)
    | throwError "iaesop(baseline): applyHyps replay selected hypothesis cannot close the target"
  let _ : Q(FromAssumption $p .in $hypType $target) := inst
  let some _ ← ProofModeM.trySynthInstanceQ q(TCOr (Affine $e) (Absorbing $target))
    | throwError
        "iaesop(baseline): applyHyps replay cannot discard the remaining context"
  have rfl : Q($e ∗ □?$p $hypType ⊣⊢ $e ∗ □?$p $hypType) := q(.rfl)
  return q(Iris.ProofMode.assumption (Q := $target) $rfl)

/- Construct an apply proof by using given hypothesis -/
partial def replayApplyCore
    {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)} {e : Q($prop)}
    (hyps : Hyps bi e) (p : Q(Bool)) (hypType target : Q($prop))
    (contexts : Array (Array IrisHyp)) (tag : Name) :
    ProofModeM (Q($e ∗ □?$p $hypType ⊢ $target) × Array MVarId) := do
  let premise ← mkFreshExprMVarQ prop

  /- Plain case no management -/
  if contexts.size <= 1 then
    let some inst ← ProofModeM.trySynthInstanceQ
        q(IntoWand $p false $hypType .out $premise .in $target)
      | do
        let hypFmt ← ppExpr hypType
        let targetFmt ← ppExpr target
        throwError m!"iaesop(baseline): applyHyps replay selected hypothesis cannot prove the target\nhyp: {hypFmt}\ntarget: {targetFmt}"
    let premise : Q($prop) ← instantiateMVars premise
    let premiseProof ← mkBIGoal hyps premise tag
    let inst : Q(IntoWand $p false $hypType .out $premise .in $target) := inst
    return (
      q(Iris.ProofMode.apply
        (P := $e) (Q := $hypType) (Q1 := $premise) (R := $target)
        (h2 := $inst)
        $premiseProof),
      #[premiseProof.mvarId!]
    )

  /- Nested case, need context management -/
  let restTarget ← mkFreshExprMVarQ prop
  let some inst ← ProofModeM.trySynthInstanceQ
      q(IntoWand $p false $hypType .out $premise .out $restTarget)
    | throwError "iaesop(baseline): applyHyps replay selected hypothesis has too few premises"
  let premise : Q($prop) ← instantiateMVars premise
  let restTarget : Q($prop) ← instantiateMVars restTarget
  let some firstContext := contexts[0]?
    | throwError "iaesop(baseline): applyHyps replay is missing the first premise context"
  let premiseNames := firstContext.map (·.name)
  let ⟨eRemaining, _, remainingHyps, premiseHyps, splitPf⟩ :=
    hyps.split bi λ name _ => premiseNames.contains name
  let premiseProof ← mkBIGoal premiseHyps premise tag
  let inst : Q(IntoWand $p false $hypType .out $premise .out $restTarget) := inst
  let step : Q($e ∗ □?$p $hypType ⊢ $eRemaining ∗ $restTarget) :=
    q(specialize_wand_subgoal
      (Q := $hypType) (P1 := $premise)
      (inst := $inst)
      $restTarget (.rfl) $splitPf $premiseProof)
  let (restProof, restGoals) ←
    replayApplyCore remainingHyps q(false) restTarget target
      (contexts.extract 1 contexts.size) tag
  return (q(Entails.trans $step $restProof), #[premiseProof.mvarId!] ++ restGoals)

/- Replay apply P by using given hyp -/
private def replayClose (goalMVarId : MVarId) (usedHyp : AppliedHyp) :
    ProofModeM (Array MVarId) := do
  goalMVarId.withContext do
    let goalType ← instantiateMVars (← goalMVarId.getType)
    let some { bi, e, hyps, goal := target, .. } := parseIrisGoal? goalType
      | throwError "iaesop(baseline): applyHyps replay expected an Iris goal"
    match usedHyp with
    | .spatial _ | .intuitionistic _ =>
      let some ⟨_, e', _, out, hypType, p, _, removePf⟩ ←
          hyps.removeG false λ name _ p _ => do
            if irisHypMatches usedHyp name p then return some ()
            else return none
        | throwError "iaesop(baseline): applyHyps replay selected Iris hypothesis disappeared"
      have : $out =Q iprop(□?$p $hypType) := ⟨⟩
      let coreProof ← mkCloseCoreProof (bi := bi) (e := e') p hypType target
      goalMVarId.assign q(($removePf).1.trans $coreProof)
      return #[]
    | .lean userName fvarId =>
      let ⟨hyp, haveProof⟩ ← mkLeanHypProof (bi := bi) (e := e) userName fvarId
      let coreProof ← mkCloseCoreProof (bi := bi) (e := e) q(true) hyp target
      goalMVarId.assign q(Entails.trans $haveProof $coreProof)
      return #[]

/- Replay apply P -∗ Q by using given hyp -/
private def replayApply (goalMVarId : MVarId) (usedHyp : AppliedHyp)
    (contexts : Array (Array IrisHyp)) : ProofModeM (Array MVarId) := do
  goalMVarId.withContext do
    let goalType ← instantiateMVars (← goalMVarId.getType)
    let some { bi, e, hyps, goal := target, .. } := parseIrisGoal? goalType
      | throwError "iaesop(baseline): applyHyps replay expected an Iris goal"
    let tag ← goalMVarId.getTag
    match usedHyp with
    | .spatial _ | .intuitionistic _ =>
      let some ⟨_, _, hyps', out, hypType, p, _, removePf⟩ ←
          hyps.removeG false λ name _ p _ => do
            if irisHypMatches usedHyp name p then return some ()
            else return none
        | throwError "iaesop(baseline): applyHyps replay selected Iris hypothesis disappeared"
      have : $out =Q iprop(□?$p $hypType) := ⟨⟩
      let (coreProof, goals) ←
        replayApplyCore (bi := bi) hyps' p hypType target contexts tag
      goalMVarId.assign q(($removePf).1.trans $coreProof)
      return goals
    | .lean userName fvarId =>
      let ⟨hyp, haveProof⟩ ← mkLeanHypProof (bi := bi) (e := e) userName fvarId
      let (coreProof, goals) ←
        replayApplyCore (bi := bi) hyps q(true) hyp target contexts tag
      goalMVarId.assign q(Entails.trans $haveProof $coreProof)
      return goals

/- [Note] Make sure you are in the correct context -/
def replay (input : RuleReplayInput) : ProofModeM (Array MVarId) := do
  let some usedHyp := input.rapp.usedHyp?
    | throwError "iaesop(baseline): applyHyps replay is missing the selected hypothesis"
  let obun ← input.rapp.children.get

  /- Distinguish the replay shape from the generated child goals -/
  if obun.goals.isEmpty || obun.kind.isInherited then
    replayClose input.goal usedHyp
  else if obun.goals.size == 1 then
    if !obun.finalizedSpatialSplits.isEmpty then
      throwError "iaesop(baseline): applyHyps replay found finalized spatial splits for a single-premise apply; expected no split information"
    replayApply input.goal usedHyp #[]
  else
    if obun.finalizedSpatialSplits.size != obun.goals.size then
      throwError s!"iaesop(baseline): applyHyps replay found {obun.finalizedSpatialSplits.size} finalized spatial splits for {obun.goals.size} generated goals"
    replayApply input.goal usedHyp obun.finalizedSpatialSplits

end Iris.ProofMode.Aesop.Rule.ApplyHyps
