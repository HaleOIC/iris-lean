module

public meta import Iris.ProofMode.Aesop.Search.SearchM
public meta import Iris.ProofMode.Tactics.Assumption
public meta import Iris.ProofMode.Tactics.Split

public meta section

namespace Iris.ProofMode.Aesop.Search

open Lean Meta Qq Std
open Iris.BI
open Iris.ProofMode

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

private def mkAssumptionProof
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
    mkAssumptionProof hyps target
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

private def findProvenRapp? (rrefs : Array RappRef) :
    SearchM Q (Option RappRef) := do
  for rref in rrefs do
    let rapp ← rref.get
    if rapp.state.isProven && !rapp.isIrrelevant then
      return some rref
  return none

private def assignSplitProofFromRapp (rapp : Rapp) : SearchM Q Unit := do
  let parent ← rapp.parent.get
  let goal : MVarId := Goal.currentMVar parent
  let assigned ← liftM (show MetaM Bool from goal.isAssignedOrDelayedAssigned)
  if assigned then
    return
  liftM do
    MVarId.withContext goal do
      let goalType ← instantiateMVars (← goal.getType)
      let some irisGoal := parseIrisGoal? goalType
        | throwError "iaesop: finalization failed, parent goal is not an Iris goal"
      let leafCount := (splitSepTargets irisGoal.goal).size
      if leafCount != rapp.irisContext.size then
        throwError
          "iaesop: finalization got {rapp.irisContext.size} context parts for {leafCount} split goals"
      let proof ← mkSplitProof irisGoal.hyps irisGoal.goal rapp.irisContext
      goal.assign proof

private partial def finalizeGoal (gref : GoalRef) : SearchM Q Unit := do
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
    assignSplitProofFromRapp rapp
  | none =>
    liftM do
      MVarId.withContext goal do
        let goalType ← instantiateMVars (← goal.getType)
        let some irisGoal := parseIrisGoal? goalType
          | throwError "iaesop: finalization failed, goal is not an Iris goal"
        let proof ← mkAssumptionProof irisGoal.hyps irisGoal.goal
        goal.assign proof

public meta def finalizeProof : SearchM Q Unit := do
  finalizeGoal (← getRootGoal)

end Iris.ProofMode.Aesop.Search
