module

public meta import Lean.Meta.Tactic.Simp.SimpAll
public meta import Iris.ProofMode.Aesop.Search.Types
public meta import Iris.ProofMode.Aesop.Search.Names
public meta import Iris.ProofMode.Aesop.Search.SearchM
public meta import Iris.ProofMode.Tactics.Cases
public meta import Iris.ProofMode.Tactics.Intro

public meta section

namespace Iris.ProofMode.Aesop

open Lean Lean.Meta Qq Std
open Iris.BI ProofMode

variable {Q : Type} [Queue Q]

private inductive NormStepResult where
  | proved
  | changed (goal : MVarId)
  | unchanged

private structure NormStepInput where
  goal : MVarId
  depth : Nat
  enableSimp : Bool
  goalMVars : Std.HashSet MVarId

private inductive NormStepKind where
  | intro
  | cases
  | simp
  deriving Inhabited, BEq, Repr

private structure NormStep where
  kind : NormStepKind
  run : NormStepInput → ProofModeM NormStepResult

private structure IrisHypInfo where
  name : Name
  ivar : IVarId
  p : Expr
  ty : Expr

private partial def collectHypInfos {u prop bi} :
    ∀ {e}, @Hyps u prop bi e → Array IrisHypInfo
  | _, .emp _ => #[]
  | _, .hyp _ name ivar p ty _ =>
    #[{ name, ivar, p := p, ty := ty }]
  | _, .sep _ _ _ _ lhs rhs =>
    collectHypInfos lhs ++ collectHypInfos rhs

private partial def collectSpatialHyps {u prop bi} :
    ∀ {e}, @Hyps u prop bi e → Array IrisHyp
  | _, .emp _ => #[]
  | _, .hyp _ name ivar p _ _ =>
    if isTrue p then #[] else #[{ name, ivar }]
  | _, .sep _ _ _ _ lhs rhs =>
    collectSpatialHyps lhs ++ collectSpatialHyps rhs

private def runIntroPat (goal : MVarId) (pat : IntroPat) :
    ProofModeM (Option MVarId) := do
  let preState ← liftM (show MetaM SavedState from saveState)
  let prePMState ← getThe ProofModeM.State
  try
    goal.withContext do
      let goalType ← instantiateMVars (← goal.getType)
      let some irisGoal := parseIrisGoal? goalType
        | return none
      let before ← getThe ProofModeM.State
      let proof ← iIntroCore irisGoal.hyps irisGoal.goal [(Syntax.missing, pat)]
      let after ← getThe ProofModeM.State
      set before
      let newGoals := after.goals.filter (!before.goals.contains ·)
      let some newGoal := newGoals.back?
        | throwError "iaesop: normalization iintro did not generate a goal"
      goal.assign proof
      return some newGoal
  catch _ =>
    set prePMState
    liftM <| preState.restore
    return none

private def runCasesPatOnHyp (goal : MVarId) (info : IrisHypInfo)
    (pat : iCasesPat) : ProofModeM (Option MVarId) := do
  let preState ← liftM (show MetaM SavedState from saveState)
  let prePMState ← getThe ProofModeM.State
  try
    goal.withContext do
      let goalType ← instantiateMVars (← goal.getType)
      let some irisGoal := parseIrisGoal? goalType
        | return none
      let some ⟨_, _e', hyps', out, ty, p, _, removePf⟩ ←
          irisGoal.hyps.removeG true fun _ ivar _ _ => do
            if ivar == info.ivar then return some ()
            else return none
        | return none
      have : $out =Q iprop(□?$p $ty) := ⟨⟩
      let newGoalRef ← IO.mkRef (none : Option MVarId)
      let proof ←
        iCasesCore irisGoal.bi hyps' irisGoal.goal pat p ty
          fun hyps goal' => do
            let newGoalExpr ← mkBIGoal hyps goal' (← goal.getTag)
            newGoalRef.set (some newGoalExpr.mvarId!)
            return newGoalExpr
      goal.assign q(($removePf).1.trans $proof)
      return (← newGoalRef.get)
  catch _ =>
    set prePMState
    liftM <| preState.restore
    return none

private def firstSuccessfulCasesStep (goal : MVarId)
    (infos : Array IrisHypInfo)
    (pat : iCasesPat)
    (eligible : IrisHypInfo → MetaM Bool) :
    ProofModeM (Option MVarId) := do
  infos.findSomeM? λ info => do
    let ok ← liftM (m := MetaM) do
      let preState ← saveState
      try
        let ok ← goal.withContext <| eligible info
        preState.restore
        return ok
      catch _ =>
        preState.restore
        return false
    if !ok then
      return none
    runCasesPatOnHyp goal info pat

private def canSplitSep (info : IrisHypInfo) : MetaM Bool := do
  let ty ← instantiateMVars info.ty
  let target := ty.consumeMData
  if target.getAppFn.constName? == some ``BIBase.sep then
    match target.getAppArgs.toList.reverse with
    | _ :: _ :: _ => return true
    | _ => return false
  return false

private def canPure {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)}
    (info : IrisHypInfo) : MetaM Bool := do
  let ty ← instantiateMVars info.ty
  let some irisTy ← checkTypeQ ty prop | return false
  let φ ← mkFreshExprMVarQ q(Prop)
  match ← ProofMode.trySynthInstanceQ q(IntoPure $irisTy $φ) with
  | .some _ => return true
  | _ => return false

private def canIntuitionistic {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)}
    (info : IrisHypInfo) : MetaM Bool := do
  if !info.p.constName? == some ``false then
    return false
  let ty ← instantiateMVars info.ty
  let some irisTy ← checkTypeQ ty prop | return false
  let persistent ← mkFreshExprMVarQ prop
  match ← ProofMode.trySynthInstanceQ
      q(IntoPersistently false $irisTy $persistent) with
  | .some _ => return true
  | _ => return false

/- `iintro`-related normalization step -/
private def introNormStep : NormStep where
  kind := .intro
  run input := do
    let names ← liftM <| collectIrisHypNames input.goal
    /- Try to find name for pure from given binder -/
    let pureName? ← liftM (m := MetaM) do
      input.goal.withContext do
        let goalType ← instantiateMVars (← input.goal.getType)
        let some irisGoal := parseIrisGoal? goalType
          | return none
        return forallBinderName? irisGoal.goal
    let pureName ←
      match pureName? with
      | some name => mkBinderFromName name
      | none => mkFreshLeanBinderFromNames names input.depth
    if let some newGoal ← runIntroPat input.goal (.intro (.pure pureName)) then
      return .changed newGoal
    let name ← mkFreshBinderFromNames names input.depth
    if let some newGoal ← runIntroPat input.goal (.intro (.one name)) then
      return .changed newGoal
    return .unchanged

/- `icases`-related normalization step -/
private def casesNormStep : NormStep where
  kind := .cases
  run input := do
    input.goal.withContext do
      let goalType ← instantiateMVars (← input.goal.getType)
      let some irisGoal := parseIrisGoal? goalType
        | return .unchanged
      let infos := collectHypInfos irisGoal.hyps
      let names := infos.map (·.name)
      let h₁ ← mkFreshBinderFromNames names input.depth
      let h₂ ← mkFreshBinderFromNames names input.depth 2
      if let some newGoal ←
          firstSuccessfulCasesStep input.goal infos
            (.conjunction [.one h₁, .one h₂]) canSplitSep then
        return .changed newGoal
      let h ← mkFreshBinderFromNames names input.depth
      if let some newGoal ←
          firstSuccessfulCasesStep input.goal infos
            (.pure h)
            (canPure (prop := irisGoal.prop) (bi := irisGoal.bi)) then
        return .changed newGoal
      let h ← mkFreshBinderFromNames names input.depth
      match ←
          firstSuccessfulCasesStep input.goal infos
            (.intuitionistic (.one h))
            (canIntuitionistic (prop := irisGoal.prop) (bi := irisGoal.bi)) with
      | some newGoal => return .changed newGoal
      | none => return .unchanged

/- Simplify normalization step -/
private def simpNormStep : NormStep where
  kind := .simp
  run input := do
    if !input.enableSimp then return .unchanged
    /- Run the whole simp step in `MetaM`, where saved states and contexts live. -/
    liftM (m := MetaM) do
      let preState ← saveState
      try
        input.goal.withContext do
          let ctx := (← Simp.mkContext {} #[← getSimpTheorems]
            <| ← getSimpCongrTheorems).setFailIfUnchanged false
          let fvarIdsToSimp := (← getLCtx).foldl (init := (#[] : Array FVarId)) λ acc ldecl =>
            if ldecl.isImplementationDetail then acc else acc.push ldecl.fvarId
          match (← Meta.simpGoal input.goal ctx (fvarIdsToSimp := fvarIdsToSimp)).1 with
          | none =>
            if !(← input.goalMVars.anyM (notM ·.isAssignedOrDelayedAssigned)) then
              return .proved
            preState.restore
            return .unchanged
          | some (_, newGoal) =>
            if newGoal == input.goal then return .unchanged
            return .changed newGoal
      catch _ =>
        preState.restore
        return .unchanged

/- [TODO] take NormStep propority into account? -/
private def normalizationSteps : Array NormStep :=
  #[introNormStep, casesNormStep, simpNormStep]

private def runFirstNormStep (input : NormStepInput) :
    ProofModeM NormStepResult := do
  let result? ← normalizationSteps.findSomeM? λ step => do
    let preState ← liftM (m := MetaM) saveState
    match ← step.run input with
    | .unchanged =>
      liftM <| preState.restore
      return none
    | result => return some result
  return result?.getD .unchanged

/- Invoked by `normalizeGoal` during search stage and `assignProof` during replay stage -/
/- [Note]: ensure already been in the correct `Meta.SavedState` before calling -/
partial def normalizeGoalMVar (goal : MVarId) (depth : Nat)
    (maxIterations : Nat) (enableSimp : Bool) (goalMVars : Std.HashSet MVarId) :
    ProofModeM NormSeqResult := do
  go 0 goal false
where
  go (iteration : Nat) (goal : MVarId) (changed : Bool) : ProofModeM NormSeqResult := do
    if iteration >= maxIterations then
      throwError "iaesop: exceeded maximum number of normalisation iterations ({maxIterations})."
    let input : NormStepInput := { goal, depth, enableSimp, goalMVars }
    match ← runFirstNormStep input with
    | .proved => return .proved
    | .changed newGoal => go (iteration + 1) newGoal true
    | .unchanged =>
      if changed then return .changed goal
      else return .unchanged

/- Search stage entry point -/
def normalizeGoal (gref : GoalRef) : SearchM Q Unit := do
  let goal ← gref.get
  match goal.normalizationState with
  | .provenByNorm .. => gref.modify λ g => g.setState .provenByNormalization
  | .normal .. => return
  | .notNormal =>
    let preGoalMVarId := goal.preNormGoal
    let config := (← readThe SearchM.Context).config
    let (result, postState, generatedSpatialHyps, usedSpatialHyps) ← liftM (m := ProofModeM) do
      goal.preNormState.restore

      /- Collect spatial hypotheses before normalization. -/
      let preHyps : Array IrisHyp ← preGoalMVarId.withContext do
        let goalType ← instantiateMVars (← preGoalMVarId.getType)
        let some irisGoal := parseIrisGoal? goalType
          | throwError "iaesop: normalization stage should be done in iris proof-mode"
        return collectSpatialHyps irisGoal.hyps

      let result ← normalizeGoalMVar preGoalMVarId goal.depth
          config.maxNormIterations config.enableSimp? goal.unassignedMvars

      /- Collect spatial hypotheses after normalization. -/
      let postHyps : Array IrisHyp ← match result with
        | .proved => pure #[]
        | .unchanged => pure preHyps
        | .changed postGoal => liftM (m := MetaM) <| postGoal.withContext do
          let goalType ← instantiateMVars (← postGoal.getType)
          let some irisGoal := parseIrisGoal? goalType
            | throwError "iaesop: normalization stage should be done in iris proof-mode"
          return collectSpatialHyps irisGoal.hyps

      let postState ← liftM (m := MetaM) saveState
      let generated := postHyps.filter λ hyp => !preHyps.contains hyp
      let consumed := preHyps.filter λ hyp => !postHyps.contains hyp
      return (result, postState, generated, consumed)

    /- According to the result, set goal-related feilds -/
    match result with
    | .proved => gref.modify λ g =>
      g.setNormalizationState (.provenByNorm postState generatedSpatialHyps usedSpatialHyps #[])
      |>.setState .provenByNormalization
    | .changed postGoal =>
      let mvars ← liftM <| postGoal.getMVarDependencies
      gref.modify λ g =>
        g.setNormalizationState (.normal postGoal postState generatedSpatialHyps usedSpatialHyps #[])
        |>.setUnassignedMvars mvars
    | .unchanged =>
      gref.modify λ g =>
        g.setNormalizationState (.normal preGoalMVarId postState #[] #[] #[])

end Aesop
