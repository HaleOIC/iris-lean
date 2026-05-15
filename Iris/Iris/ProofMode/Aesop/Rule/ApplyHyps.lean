module

public meta import Iris.ProofMode.Aesop.Rule.Common
public meta import Iris.ProofMode.Tactics.HaveCore

public meta section

namespace Iris.ProofMode.Aesop.Rule.ApplyHyps

open Lean Meta Qq Std
open Iris.BI
open Iris.ProofMode
open Iris.ProofMode.Aesop

variable {Q : Type} [Queue Q]

private inductive ApplySource where
  | iris (hyp : IrisHyp)
  | lean (userName : Name) (fvarId : FVarId)

private structure ApplyHypCandidate where
  source : ApplySource
  premises : Array Expr

private def ApplySource.name : ApplySource → Name
  | .iris hyp => hyp.name
  | .lean userName _ => userName

private def ApplySource.consumedSpatialHyp? : ApplySource → Option IrisHyp
  | .iris hyp => some hyp
  | .lean .. => none

private def ApplySource.consumedLeanHyp? : ApplySource → Option FVarId
  | .iris .. => none
  | .lean _ fvarId => some fvarId

private partial def collectIntoWandPremises?
    {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)}
    (p : Q(Bool)) (hypType target : Q($prop)) :
    MetaM (Option (Array Expr)) := do
  let hypTypeExpr ← instantiateMVars hypType
  let targetExpr ← instantiateMVars target
  let some hypType ← checkTypeQ hypTypeExpr prop
    | throwError "iaesop: internal error: applyHyps hypothesis has wrong type"
  let some target ← checkTypeQ targetExpr prop
    | throwError "iaesop: internal error: applyHyps target has wrong type"
  let preState ← saveState
  let premise ← mkFreshExprMVarQ prop
  let premiseExpr : Expr := premise
  match ← ProofMode.trySynthInstanceQ
      q(IntoWand $p false $hypType .out $premise .in $target) with
  | .some _ => return some #[premiseExpr]
  | .none | .undef => restoreState preState
  let preState ← saveState
  let premise ← mkFreshExprMVarQ prop
  let premiseExpr : Expr := premise
  let restTarget ← mkFreshExprMVarQ prop
  match ← ProofMode.trySynthInstanceQ
      q(IntoWand $p false $hypType .out $premise .out $restTarget) with
  | .none | .undef =>
    restoreState preState
    return none
  | .some _ =>
    match ← collectIntoWandPremises? (bi := bi) q(false) restTarget target with
    | some premises => return some (#[premiseExpr] ++ premises)
    | none =>
      restoreState preState
      return none

private def collectIrisApplyHypCandidate?
    {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)}
    (target : Q($prop)) (name : Name) (ivar : IVarId)
    (p : Q(Bool)) (ty : Q($prop)) :
    MetaM (Option ApplyHypCandidate) := do
  let preState ← saveState
  let some premises ← collectIntoWandPremises? (bi := bi) p ty target
    | restoreState preState; return none
  if premises.isEmpty then
    restoreState preState
    return none
  return some {
    source := .iris { name, ivar }
    premises
  }

private partial def collectIrisApplyHypCandidates
    {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)}
    (target : Q($prop)) :
    ∀ {e}, @Hyps u prop bi e → MetaM (Array ApplyHypCandidate)
  | _, .emp _ => return #[]
  | _, .hyp _ name ivar p ty _ => do
    match ← collectIrisApplyHypCandidate? (bi := bi) target name ivar p ty with
    | some candidate => return #[candidate]
    | none => return #[]
  | _, .sep _ _ _ _ lhs rhs => do
    return (← collectIrisApplyHypCandidates target lhs) ++
      (← collectIrisApplyHypCandidates target rhs)

private def collectLeanApplyHypCandidate?
    {u : Level} {prop : Q(Type u)} (bi : Q(BI $prop))
    (target : Q($prop)) (decl : LocalDecl) :
    MetaM (Option ApplyHypCandidate) := do
  let preState ← saveState
  let val := mkFVar decl.fvarId
  let ty ← instantiateMVars (← inferType val)
  let ⟨newMVars, _, _⟩ ← forallMetaTelescope ty
  let val := mkAppN val newMVars
  let ty ← instantiateMVars (← inferType val)
  if ! (← Meta.isProp ty) then
    restoreState preState
    return none
  have ty : Q(Prop) := ty
  let hyp ← mkFreshExprMVarQ prop
  match ← ProofMode.trySynthInstanceQ
      q(AsEmpValid .into $ty .in $prop .in $bi $hyp) with
  | .none | .undef =>
    restoreState preState
    return none
  | .some _ =>
    let some premises ← collectIntoWandPremises? (bi := bi) q(true) hyp target
      | restoreState preState; return none
    if premises.isEmpty then
      restoreState preState
      return none
    return some {
      source := .lean decl.userName decl.fvarId
      premises
    }

private def collectLeanApplyHypCandidates
    {u : Level} {prop : Q(Type u)} (bi : Q(BI $prop))
    (target : Q($prop)) :
    MetaM (Array ApplyHypCandidate) := do
  let mut candidates := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then
      continue
    if let some candidate ← collectLeanApplyHypCandidate? bi target decl then
      candidates := candidates.push candidate
  return candidates

private def mkApplyHypChildren (goal : MVarId) :
    MetaM (Option (Array (ApplyHypCandidate × Array ChildGoalSpec))) := do
  goal.withContext do
    let goalType ← instantiateMVars (← goal.getType)
    let some irisGoal := parseIrisGoal? goalType
      | return none
    let targetExpr ← instantiateMVars irisGoal.goal
    let some target ← checkTypeQ targetExpr irisGoal.prop
      | throwError "iaesop: internal error: applyHyps target has wrong type"
    let irisCandidates ← collectIrisApplyHypCandidates target irisGoal.hyps
    let leanCandidates ← collectLeanApplyHypCandidates irisGoal.bi target
    let candidates := irisCandidates ++ leanCandidates
    if candidates.isEmpty then
      return none
    let tag ← goal.getTag
    some <$> candidates.mapM λ candidate => do
      let ctx ←
        (match candidate.source with
        | .iris hyp => do
          let some ⟨_, e', hyps', _, _, _, _, _⟩ ←
              irisGoal.hyps.removeG true fun _ ivar _ _ => do
                if ivar == hyp.ivar then return some ()
                else return none
            | throwError "iaesop: internal error: applyHyps candidate disappeared"
          return Sigma.mk e' hyps'
        | .lean .. => do
          return Sigma.mk irisGoal.e irisGoal.hyps :
          MetaM (Sigma fun e' : Q($irisGoal.prop) => Hyps irisGoal.bi e'))
      let e' := ctx.1
      let hyps' := ctx.2
      let children ← candidate.premises.mapM λ premiseExpr => do
        let premiseExpr ← instantiateMVars premiseExpr
        let some premise ← checkTypeQ premiseExpr irisGoal.prop
          | throwError "iaesop: internal error: applyHyps premise has wrong type"
        let childIrisGoal := {
          irisGoal with
          e := e'
          hyps := hyps'
          goal := premise
        }
        let goalExpr ← mkFreshExprSyntheticOpaqueMVar (IrisGoal.toExpr childIrisGoal) tag
        let goal := goalExpr.mvarId!
        return {
          goal
          irisGoal := childIrisGoal
          mvars := ← goal.getMVarDependencies
        }
      return (candidate, children)

def run (parentRef : GoalRef) (_matchResult : RuleMatch) :
    SearchM Q (Array RappSpec) := do
  let parent ← parentRef.get
  let (goal, state) ← normalizedGoalAndState "applyHyps" parent
  let (some expansions, postState) ← liftM do
      restoreState state
      let children? ← mkApplyHypChildren goal
      let postState ← saveState
      return (children?, postState)
    | return #[]

  expansions.mapM λ (candidate, children) => do
    dbg_trace s!"applyHyps selected {candidate.source.name} and generated {children.size} goals"
    for child in children do
      let targetFmt ← liftM <| ppExpr child.irisGoal.goal
      dbg_trace s!"  applyHyps child target: {targetFmt.pretty}"
    return {
      rappState := .unknown
      obunState := .unknown
      obunKind := .managed
      childGoals := children
      fullContextIrisSubgoals := children.map (·.irisGoal)
      consumedSpatialHyp? := candidate.source.consumedSpatialHyp?
      consumedLeanHyp? := candidate.source.consumedLeanHyp?
      finalizedSpatialSplits := children.map (λ _ => #[])
      metaState := postState
    }

end Iris.ProofMode.Aesop.Rule.ApplyHyps
