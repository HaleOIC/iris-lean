module

public meta import Lean.Meta.Tactic.Simp.SimpAll
public meta import Iris.ProofMode.Aesop.Search.Shared.CoreM
public meta import Iris.ProofMode.Tactics.Assumption
public meta import Iris.ProofMode.Tactics.Apply
public meta import Iris.ProofMode.Tactics.HaveCore
public meta import Iris.ProofMode.Tactics.Pure
public meta import Iris.ProofMode.Tactics.Split

public meta section

namespace Iris.ProofMode.Aesop.Search.Copy

open Lean Meta Qq Std
open Iris.BI
open Iris.ProofMode
open Iris.ProofMode.Aesop

variable {Q : Type} [Queue Q]

private def Goal.currentMVar (g : Goal) : MVarId :=
  g.normalizationState.normalizedGoal?.getD g.preNormGoal

private partial def splitSepTargets (target : Expr) : Array Expr :=
  let target := target.consumeMData
  if target.getAppFn.constName? == some ``BIBase.sep then
    match target.getAppArgs.toList.reverse with
    | rhs :: lhs :: _ => splitSepTargets lhs ++ splitSepTargets rhs
    | _ => #[target]
  else
    #[target]

private def splitSepTarget? (target : Expr) : Option (Expr × Expr) :=
  let target := target.consumeMData
  if target.getAppFn.constName? == some ``BIBase.sep then
    match target.getAppArgs.toList.reverse with
    | rhs :: lhs :: _ => some (lhs, rhs)
    | _ => none
  else
    none

private def collectIVars (contexts : Array (Array IrisHyp)) : Array IVarId :=
  contexts.foldl (init := #[]) λ ivars hyps =>
    hyps.foldl (init := ivars) λ ivars hyp => ivars.push hyp.ivar

private def mkDirectAssumptionProof
    {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)} {e : Q($prop)}
    (hyps : Hyps bi e) (target : Q($prop)) :
    MetaM Q($e ⊢ $target) := do
  let some ⟨inst, e', _, out, ty, b, _, pf⟩ ←
      hyps.removeG true fun _ _ b ty => do
        let .some (inst, _) ←
            ProofMode.trySynthInstanceQ q(FromAssumption $b .in $ty $target)
          | return none
        return some inst
    | throwError "iaesop: finalization failed, no matching assumption for {target}"
  let _ : Q(FromAssumption $b .in $ty $target) := inst
  have : $out =Q iprop(□?$b $ty) := ⟨⟩
  let .some _ ← trySynthInstanceQ q(TCOr (Affine $e') (Absorbing $target))
    | throwError
        "iaesop: finalization failed, unused context is not affine and target is not absorbing"
  return q(Iris.ProofMode.assumption (Q := $target) $pf)

private def mkPropProof? (φ : Q(Prop)) : MetaM (Option Q($φ)) := do
  let proof : Q($φ) ← mkFreshExprMVar φ
  let goal := proof.mvarId!
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    let preState ← saveState
    for ldecl in ← getLCtx do
      if ldecl.isImplementationDetail then
        continue
      restoreState preState
      let hypType ← instantiateMVars ldecl.type
      if ← isDefEq hypType target then
        goal.assign (mkFVar ldecl.fvarId)
        return some proof
    restoreState preState
    let ctx ← Simp.mkContext
      (config := ({} : Simp.Config))
      (simpTheorems := #[← getSimpTheorems])
      (congrTheorems := ← getSimpCongrTheorems)
    let ctx := ctx.setFailIfUnchanged false
    let (result?, _) ←
      Meta.simpGoal goal ctx (simprocs := #[]) (discharge? := none)
        (simplifyTarget := true) (fvarIdsToSimp := #[])
    match result? with
    | none => return some proof
    | some _ =>
      restoreState preState
      return none

private def mkPureProof?
    {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)} {e : Q($prop)}
    (_hyps : Hyps bi e) (target : Q($prop)) :
    MetaM (Option Q($e ⊢ $target)) := do
  let b : Q(Bool) ← mkFreshExprMVarQ q(Bool)
  let φ : Q(Prop) ← mkFreshExprMVarQ q(Prop)
  let .some (h, _) ← ProofMode.trySynthInstanceQ q(FromPure $b $target .out $φ)
    | return none
  let h : Q(FromPure $b $target .out $φ) := h
  let some proof ← mkPropProof? φ
    | return none
  match ← whnf b with
  | .const ``true _ =>
    have : $b =Q true := ⟨⟩
    let .some _ ← trySynthInstanceQ q(Affine $e)
      | return none
    return some q(pure_intro_affine (P := $e) (Q := $target) $h $proof)
  | .const ``false _ =>
    have : $b =Q false := ⟨⟩
    return some q(pure_intro_spatial (P := $e) (Q := $target) $h $proof)
  | _ =>
    return none

private partial def mkAssumptionProof
    {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)} {e : Q($prop)}
    (hyps : Hyps bi e) (target : Q($prop)) :
    MetaM Q($e ⊢ $target) := do
  try
    mkDirectAssumptionProof hyps target
  catch _ =>
    let some ⟨(inst, premise), e', hyps', out, hypType, p, _, removePf⟩ ←
        hyps.removeG true fun _ _ p hypType => do
          let premise ← mkFreshExprMVarQ prop
          let .some (inst, _) ← ProofMode.trySynthInstanceQ
              q(IntoWand $p false $hypType .out $premise .in $target)
            | return none
          return some (inst, premise)
      | throwError "iaesop: finalization failed, no matching assumption for {target}"
    have : $out =Q iprop(□?$p $hypType) := ⟨⟩
    let premiseProof ← mkAssumptionProof hyps' premise
    let inst' : Q(IntoWand $p false $hypType .out $premise .in $target) := inst
    return q(($removePf).1.trans (Iris.ProofMode.apply
      (P := $e') (Q := $hypType) (Q1 := $premise) (R := $target)
      (h2 := $inst')
      $premiseProof))

private partial def mkSplitProof
    {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)} {e : Q($prop)}
    (hyps : Hyps bi e) (target : Q($prop))
    (contexts : Array (Array IrisHyp)) :
    MetaM Q($e ⊢ $target) := do
  let targetExpr ← instantiateMVars target
  match splitSepTarget? targetExpr with
  | none =>
    if contexts.size != 1 then
      throwError
        "iaesop: finalization expected one context part for atomic target, got {contexts.size}"
    match ← mkPureProof? hyps target with
    | some proof => return proof
    | none => mkAssumptionProof hyps target
  | some (lhsExpr, rhsExpr) =>
    let lhsCount := (splitSepTargets lhsExpr).size
    let lhsContexts := contexts.extract 0 lhsCount
    let rhsContexts := contexts.extract lhsCount contexts.size
    let some lhsTarget ← checkTypeQ lhsExpr prop
      | throwError "iaesop: finalization failed, left split target has wrong type"
    let some rhsTarget ← checkTypeQ rhsExpr prop
      | throwError "iaesop: finalization failed, right split target has wrong type"
    let .some _ ← trySynthInstanceQ q(FromSep $target $lhsTarget $rhsTarget)
      | throwError "iaesop: finalization failed, target is not a separating conjunction"
    let rightIVars := collectIVars rhsContexts
    let ⟨_, _, lhsHyps, rhsHyps, pf⟩ :=
      hyps.split bi fun _ ivar => rightIVars.contains ivar
    let lhsProof ← mkSplitProof lhsHyps lhsTarget lhsContexts
    let rhsProof ← mkSplitProof rhsHyps rhsTarget rhsContexts
    return q(sep_split (Q := $target) $pf $lhsProof $rhsProof)

private partial def mkApplyHypCoreProof
    {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)} {e : Q($prop)}
    (hyps : Hyps bi e) (p : Q(Bool)) (hypType : Q($prop))
    (target : Q($prop)) (premises : Array IrisGoal)
    (contexts : Array (Array IrisHyp)) :
    MetaM Q($e ∗ □?$p $hypType ⊢ $target) := do
  if premises.size != contexts.size then
    throwError
      "iaesop: finalization got {contexts.size} context parts for {premises.size} apply premises"
  if premises.isEmpty then
    let .some (inst, _) ← ProofMode.trySynthInstanceQ
        q(FromAssumption $p .in $hypType $target)
      | throwError "iaesop: finalization failed, selected hypothesis cannot directly prove target"
    let _ : Q(FromAssumption $p .in $hypType $target) := inst
    let .some _ ← trySynthInstanceQ q(TCOr (Affine $e) (Absorbing $target))
      | throwError "iaesop: finalization failed, unused context is not affine and target is not absorbing"
    have rfl : Q($e ∗ □?$p $hypType ⊣⊢ $e ∗ □?$p $hypType) := q(.rfl)
    return q(Iris.ProofMode.assumption (Q := $target) $rfl)
  let some firstPremise := premises[0]?
    | throwError "iaesop: finalization cannot apply a hypothesis without premises"
  let some firstContext := contexts[0]?
    | throwError "iaesop: finalization cannot apply a hypothesis without premise context"
  let premiseTargetExpr ← instantiateMVars firstPremise.goal
  let some premiseTarget ← checkTypeQ premiseTargetExpr prop
    | throwError "iaesop: finalization failed, apply premise has wrong type"
  if premises.size == 1 then
    let tcPremise ← mkFreshExprMVarQ prop
    let .some (inst, _) ← ProofMode.trySynthInstanceQ
        q(IntoWand $p false $hypType .out $tcPremise .in $target)
      | throwError "iaesop: finalization failed, selected hypothesis cannot prove target"
    unless ← isDefEq tcPremise premiseTarget do
      throwError "iaesop: finalization wand premise does not match generated subgoal"
    let premiseProof : Q($e ⊢ $tcPremise) ←
      mkSplitProof hyps tcPremise #[firstContext]
    let _ : Q(IntoWand $p false $hypType .out $tcPremise .in $target) := inst
    return q(Iris.ProofMode.apply
      (P := $e) (Q := $hypType) (Q1 := $tcPremise) (R := $target)
      (h2 := $inst)
      $premiseProof)

  let firstIVars := firstContext.map (·.ivar)
  let ⟨eRemaining, ePremise, remainingHyps, premiseHyps, splitPf⟩ :=
    hyps.split bi fun _ ivar => firstIVars.contains ivar
  let tcPremise ← mkFreshExprMVarQ prop
  let restTarget ← mkFreshExprMVarQ prop
  let .some (inst, _) ← ProofMode.trySynthInstanceQ
      q(IntoWand $p false $hypType .out $tcPremise .out $restTarget)
    | throwError "iaesop: finalization failed, selected hypothesis has incompatible premise"
  unless ← isDefEq tcPremise premiseTarget do
    throwError "iaesop: finalization wand premise does not match generated subgoal"
  let premiseProof : Q($ePremise ⊢ $tcPremise) ←
    mkSplitProof premiseHyps tcPremise #[firstContext]
  let _ : Q(IntoWand $p false $hypType .out $tcPremise .out $restTarget) := inst
  let step : Q($e ∗ □?$p $hypType ⊢ $eRemaining ∗ $restTarget) :=
    q(specialize_wand_subgoal
      (Q := $hypType) (P1 := $tcPremise)
      (inst := $inst)
      $restTarget (.rfl) $splitPf $premiseProof)
  let restPremises := premises.extract 1 premises.size
  let restContexts := contexts.extract 1 contexts.size
  let restProof ←
    mkApplyHypCoreProof remainingHyps q(false) restTarget target restPremises restContexts
  return q(Entails.trans $step $restProof)

private def mkApplyHypProof
    {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)} {e : Q($prop)}
    (hyps : Hyps bi e) (target : Q($prop)) (applyHyp : IrisHyp)
    (premises : Array IrisGoal) (contexts : Array (Array IrisHyp)) :
    MetaM Q($e ⊢ $target) := do
  let some ⟨_, _, hyps', out, hypType, p, _, removePf⟩ ←
      hyps.removeG true fun _ ivar _ _ => do
        if ivar == applyHyp.ivar then return some ()
        else return none
    | throwError "iaesop: finalization failed, selected apply hypothesis disappeared"
  have : $out =Q iprop(□?$p $hypType) := ⟨⟩
  let coreProof ←
    mkApplyHypCoreProof hyps' p hypType target premises contexts
  return q(($removePf).1.trans $coreProof)

private def mkLeanApplyHypProof
    {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)} {e : Q($prop)}
    (hyps : Hyps bi e) (target : Q($prop)) (fvarId : FVarId)
    (premises : Array IrisGoal) (contexts : Array (Array IrisHyp)) :
    MetaM Q($e ⊢ $target) := do
  let val := mkFVar fvarId
  let ty ← instantiateMVars (← inferType val)
  let ⟨newMVars, _, _⟩ ← forallMetaTelescope ty
  let val := mkAppN val newMVars
  let ty ← instantiateMVars (← inferType val)
  if ! (← Meta.isProp ty) then
    throwError "iaesop: finalization failed, Lean apply hypothesis is not a proposition"
  have ty : Q(Prop) := ty
  have val : Q($ty) := val
  let hyp ← mkFreshExprMVarQ prop
  let .some (inst, _) ← ProofMode.trySynthInstanceQ
      q(AsEmpValid .into $ty .in $prop .in $bi $hyp)
    | throwError
        "iaesop: finalization failed, Lean apply hypothesis is not an Iris entailment"
  let inst : Q(AsEmpValid .into $ty .in $prop .in $bi $hyp) := inst
  let haveProof : Q($e ⊢ $e ∗ □ $hyp) :=
    q(have_asEmpValid (P := $hyp) (Q := $e) (h1 := $inst) $val)
  let coreProof ←
    mkApplyHypCoreProof hyps q(true) hyp target premises contexts
  return q(Entails.trans $haveProof $coreProof)

private def findProvenRapp? (rrefs : Array RappRef) :
    CoreM Q (Option RappRef) := do
  for rref in rrefs do
    let rapp ← rref.get
    if rapp.state.isProven && !rapp.isIrrelevant then
      return some rref
  return none

private def assignProofFromRapp (rapp : Rapp) : CoreM Q Unit := do
  let parent ← rapp.parent.get
  let childObun ← rapp.children.get
  let fullContextIrisSubgoals := childObun.fullContextIrisSubgoals
  let finalizedSpatialSplits := childObun.finalizedSpatialSplits
  liftM (show MetaM Unit from restoreState rapp.metaState)
  let goal : MVarId := Goal.currentMVar parent
  let assigned ← liftM (show MetaM Bool from goal.isAssignedOrDelayedAssigned)
  if assigned then
    return
  liftM do
    MVarId.withContext goal do
      let goalType ← instantiateMVars (← goal.getType)
      let some irisGoal := parseIrisGoal? goalType
        | throwError "iaesop: finalization failed, parent goal is not an Iris goal"
      let proof ←
        match rapp.usedHyp? with
        | none =>
          let leafCount := (splitSepTargets irisGoal.goal).size
          if leafCount != finalizedSpatialSplits.size then
            throwError
              "iaesop: finalization got {finalizedSpatialSplits.size} context parts for {leafCount} split goals"
          mkSplitProof irisGoal.hyps irisGoal.goal finalizedSpatialSplits
        | some (.spatial applyHyp) | some (.intuitionistic applyHyp) =>
          mkApplyHypProof irisGoal.hyps irisGoal.goal applyHyp
            fullContextIrisSubgoals finalizedSpatialSplits
        | some (.lean _ fvarId) =>
          mkLeanApplyHypProof irisGoal.hyps irisGoal.goal fvarId
            fullContextIrisSubgoals finalizedSpatialSplits
      goal.assign proof

private partial def finalizeGoal (gref : GoalRef) : CoreM Q Unit := do
  let goalNode ← gref.get
  if !goalNode.state.isProven then
    throwError "iaesop: finalization reached an unproven goal"
  let goal : MVarId := Goal.currentMVar goalNode
  let assigned ← liftM (show MetaM Bool from goal.isAssignedOrDelayedAssigned)
  if assigned then
    return
  match ← findProvenRapp? goalNode.children with
  | some rref =>
    let rapp ← rref.get
    assignProofFromRapp rapp
  | none =>
    liftM do
      MVarId.withContext goal do
        let goalType ← instantiateMVars (← goal.getType)
        let some irisGoal := parseIrisGoal? goalType
          | throwError "iaesop: finalization failed, goal is not an Iris goal"
        let proof ← mkAssumptionProof irisGoal.hyps irisGoal.goal
        goal.assign proof

public meta def finalizeProof : CoreM Q Unit := do
  let root ← getRootGoal
  finalizeGoal root

end Iris.ProofMode.Aesop.Search.Copy
