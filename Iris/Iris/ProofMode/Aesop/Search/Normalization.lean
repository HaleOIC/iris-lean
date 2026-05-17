module

public meta import Lean.Meta.Tactic.Simp.SimpAll
public meta import Iris.ProofMode.Aesop.Names
public meta import Iris.ProofMode.Aesop.Search.SearchM
public meta import Iris.ProofMode.Tactics.Cases
public meta import Iris.ProofMode.Tactics.Intro

public meta section

namespace Iris.ProofMode.Aesop

open Lean Lean.Meta Qq Std
open Iris.BI ProofMode

variable {Q : Type} [Queue Q]

private structure IrisHypInfo where
  name : Name
  ivar : IVarId
  p : Expr
  ty : Expr

private def IrisHypInfo.isSpatial (info : IrisHypInfo) : Bool :=
  info.p.constName? == some ``false

private partial def collectHypInfos {u prop bi} :
    ∀ {e}, @Hyps u prop bi e → Array IrisHypInfo
  | _, .emp _ => #[]
  | _, .hyp _ name ivar p ty _ =>
    #[{ name, ivar, p := p, ty := ty }]
  | _, .sep _ _ _ _ lhs rhs =>
    collectHypInfos lhs ++ collectHypInfos rhs

private def sepParts? (target : Expr) : Option (Expr × Expr) :=
  let target := target.consumeMData
  if target.getAppFn.constName? == some ``BIBase.sep then
    match target.getAppArgs.toList.reverse with
    | rhs :: lhs :: _ => some (lhs, rhs)
    | _ => none
  else
    none

private def mkFreshBinder (goal : MVarId) (pref : Name) :
    ProofModeM (TSyntax ``binderIdent) := do
  let ident ← liftM <| freshIdentM goal pref
  `(binderIdent| $ident:ident)

private def splitName (name : Name) (suffix : String) : Name :=
  let name := name.eraseMacroScopes
  if name.isAnonymous then
    (`H).appendAfter suffix
  else
    name.appendAfter suffix

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

private def tryIntro (goal : MVarId) : ProofModeM (Option MVarId) := do
  let pureName ← mkFreshBinder goal `h
  if let some newGoal ← runIntroPat goal (.intro (.pure pureName)) then
    return some newGoal
  let name ← mkFreshBinder goal `H
  runIntroPat goal (.intro (.one name))

private def splitPat (goal : MVarId) (info : IrisHypInfo) :
    ProofModeM iCasesPat := do
  let h₁ ← mkFreshBinder goal (splitName info.name "_l")
  let h₂ ← mkFreshBinder goal (splitName info.name "_r")
  return .conjunction [.one h₁, .one h₂]

private def purePat (goal : MVarId) (info : IrisHypInfo) :
    ProofModeM iCasesPat := do
  return .pure (← mkFreshBinder goal (splitName info.name "_pure"))

private def intuitionisticPat (goal : MVarId) (info : IrisHypInfo) :
    ProofModeM iCasesPat := do
  return .intuitionistic (.one (← mkFreshBinder goal (splitName info.name "_pers")))

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

private def checkEligible (goal : MVarId)
    (eligible : IrisHypInfo → MetaM Bool) (info : IrisHypInfo) :
    ProofModeM Bool := do
  liftM do
    let preState ← saveState
    try
      let ok ← goal.withContext <| eligible info
      preState.restore
      return ok
    catch _ =>
      preState.restore
      return false

private def firstSuccessfulCasesStep (goal : MVarId)
    (infos : Array IrisHypInfo)
    (mkPat : IrisHypInfo → ProofModeM iCasesPat)
    (eligible : IrisHypInfo → MetaM Bool) :
    ProofModeM (Option MVarId) := do
  for info in infos do
    unless ← checkEligible goal eligible info do
      continue
    let pat ← mkPat info
    if let some newGoal ← runCasesPatOnHyp goal info pat then
      return some newGoal
  return none

private def canSplitSep (info : IrisHypInfo) : MetaM Bool := do
  let ty ← instantiateMVars info.ty
  return sepParts? ty |>.isSome

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
  if !info.isSpatial then
    return false
  let ty ← instantiateMVars info.ty
  let some irisTy ← checkTypeQ ty prop | return false
  let persistent ← mkFreshExprMVarQ prop
  match ← ProofMode.trySynthInstanceQ
      q(IntoPersistently false $irisTy $persistent) with
  | .some _ => return true
  | _ => return false

private def tryCasesStep (goal : MVarId) : ProofModeM (Option MVarId) := do
  goal.withContext do
    let goalType ← instantiateMVars (← goal.getType)
    let some irisGoal := parseIrisGoal? goalType
      | return none
    let infos := collectHypInfos irisGoal.hyps
    if let some newGoal ←
        firstSuccessfulCasesStep goal infos (splitPat goal) canSplitSep then
      return some newGoal
    if let some newGoal ←
        firstSuccessfulCasesStep goal infos (purePat goal)
          (canPure (prop := irisGoal.prop) (bi := irisGoal.bi)) then
      return some newGoal
    firstSuccessfulCasesStep goal infos (intuitionisticPat goal)
      (canIntuitionistic (prop := irisGoal.prop) (bi := irisGoal.bi))

private inductive SimpNormResult where
  | solved
  | unchanged
  | simplified (newGoal : MVarId)

private def simpGoalWithAllHypotheses (goal : MVarId) :
    MetaM SimpNormResult := do
  goal.withContext do
    let ctx ← Simp.mkContext
      (config := ({} : Simp.Config))
      (simpTheorems := #[← getSimpTheorems])
      (congrTheorems := ← getSimpCongrTheorems)
    let ctx := ctx.setFailIfUnchanged false
    let lctx ← getLCtx
    let mut fvarIdsToSimp := Array.mkEmpty lctx.decls.size
    for ldecl in lctx do
      if ldecl.isImplementationDetail then
        continue
      fvarIdsToSimp := fvarIdsToSimp.push ldecl.fvarId
    let (result?, _) ←
      Meta.simpGoal goal ctx (simprocs := #[]) (discharge? := none)
        (simplifyTarget := true) (fvarIdsToSimp := fvarIdsToSimp)
    match result? with
    | none =>
      return .solved
    | some (_, newGoal) =>
      if newGoal == goal then
        return .unchanged
      else
        return .simplified newGoal

private def anyMVarDropped (goalMVars : Std.HashSet MVarId) : MetaM Bool := do
  for mvar in goalMVars do
    if !(← mvar.isAssignedOrDelayedAssigned) then
      return true
  return false

private inductive NormStepResult where
  | proved
  | changed (goal : MVarId)
  | unchanged

private def trySimp (goal : MVarId) (goalMVars : Std.HashSet MVarId) :
    ProofModeM NormStepResult := do
  let hasSpatialHyp ← liftM <| goal.withContext do
    let goalType ← instantiateMVars (← goal.getType)
    let some irisGoal := parseIrisGoal? goalType
      | return false
    return (collectHypInfos irisGoal.hyps).any (·.isSpatial)
  if hasSpatialHyp then
    return .unchanged
  let preState ← liftM (show MetaM SavedState from saveState)
  try
    match ← liftM <| simpGoalWithAllHypotheses goal with
    | .solved =>
      if ← liftM <| anyMVarDropped goalMVars then
        liftM <| preState.restore
        return .unchanged
      return .proved
    | .simplified newGoal =>
      return .changed newGoal
    | .unchanged =>
      return .unchanged
  catch _ =>
    liftM <| preState.restore
    return .unchanged

private inductive NormSeqResult where
  | proved
  | changed (goal : MVarId)
  | unchanged

private partial def normalizeGoalMVar (goal : MVarId) (maxIterations : Nat)
    (enableSimp : Bool) (goalMVars : Std.HashSet MVarId) :
    ProofModeM NormSeqResult := do
  go 0 goal false
where
  go (iteration : Nat) (goal : MVarId) (changed : Bool) :
      ProofModeM NormSeqResult := do
    if iteration >= maxIterations then
      throwError
        "iaesop: exceeded maximum number of normalisation iterations ({maxIterations})."
    let preState ← liftM (show MetaM SavedState from saveState)
    match ← tryIntro goal with
    | some newGoal =>
      go (iteration + 1) newGoal true
    | none =>
      liftM <| preState.restore
      match ← tryCasesStep goal with
      | some newGoal =>
        go (iteration + 1) newGoal true
      | none =>
        if enableSimp then
          match ← trySimp goal goalMVars with
          | .proved => return .proved
          | .changed newGoal => go (iteration + 1) newGoal true
          | .unchanged =>
            if changed then return .changed goal
            else return .unchanged
        else
          if changed then return .changed goal
          else return .unchanged

def normalizeGoal (gref : GoalRef) : SearchM Q Unit := do
  let g ← gref.get
  let preGoal := g.preNormGoal
  match g.normalizationState with
  | .provenByNorm .. =>
    gref.modify λ g => g.setState .provenByNormalization
  | .normal .. =>
    return
  | .notNormal =>
    let config := (← readThe SearchM.Context).config
    let (result, postState) ← liftM (show ProofModeM _ from do
      liftM <| g.preNormState.restore
      let result ←
        normalizeGoalMVar preGoal config.maxNormIterations config.enableSimp?
          g.unassignedMvars
      let postState ← liftM (show MetaM SavedState from saveState)
      return (result, postState))
    match result with
    | .proved =>
      gref.modify λ g =>
        g.setNormalizationState (.provenByNorm postState #[])
          |>.setState .provenByNormalization
    | .changed postGoal =>
      let mvars ← liftM <| postGoal.getMVarDependencies
      gref.modify λ g =>
        g.setNormalizationState (.normal postGoal postState #[])
          |>.setUnassignedMvars mvars
    | .unchanged =>
      gref.modify λ g =>
        g.setNormalizationState (.normal preGoal postState #[])

end Aesop
