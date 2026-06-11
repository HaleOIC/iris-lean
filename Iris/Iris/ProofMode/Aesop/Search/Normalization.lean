module

public meta import Lean.Meta.Tactic.Simp.SimpAll
public meta import Iris.ProofMode.Aesop.Script.Basic
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

/-- Render an `iCasesPat` back into surface syntax so that normalization steps
can be reported as concrete `icases`/`iintro` tactics in `iaesop?` scripts. -/
private partial def renderICasesPat : iCasesPat → MetaM (TSyntax `icasesPat)
  | .one name => `(icasesPat| $name:binderIdent)
  | .pure name => `(icasesPat| %$name:binderIdent)
  | .clear => `(icasesPat| -)
  | .intuitionistic p => do let q ← renderICasesPat p; `(icasesPat| #$q)
  | .spatial p => do let q ← renderICasesPat p; `(icasesPat| ∗$q)
  | .mod p => do let q ← renderICasesPat p; `(icasesPat| >$q)
  | .conjunction ps => do
      let alts ← ps.toArray.mapM fun p => do
        let q ← renderICasesPat p
        `(icasesPatAlts| $q:icasesPat)
      `(icasesPat| ⟨$alts,*⟩)
  | .disjunction ps => do
      let qs ← ps.toArray.mapM renderICasesPat
      `(icasesPat| ($qs|*))
  | .frame => `(icasesPat| -)

/-- Build the `iintro` tactic syntax corresponding to a normalization intro. -/
private def mkIntroTactic (pat : IntroPat) : MetaM (TSyntax `tactic) := do
  match pat with
  | .intro casesPat =>
      let p ← renderICasesPat casesPat
      `(tactic| iintro $p:icasesPat)
  | .trivial => `(tactic| iintro //)
  | .modintro => `(tactic| iintro !>)

/-- Build the `icases` tactic syntax for a normalization case split on `hyp`. -/
private def mkICasesTactic (hyp : Name) (pat : iCasesPat) :
    MetaM (TSyntax `tactic) := do
  let p ← renderICasesPat pat
  let hypIdent := mkIdent hyp
  `(tactic| icases $hypIdent:term with $p:icasesPat)

/-- As `mkICasesTactic`, but only when script recording is requested. -/
private def mkICasesTactic? (record : Bool) (hyp : Name) (pat : iCasesPat) :
    MetaM (Option (TSyntax `tactic)) :=
  if record then some <$> mkICasesTactic hyp pat else pure none

private inductive NormStepResult where
  | proved
  | changed (goal : MVarId) (tactic? : Option (TSyntax `tactic))
  | unchanged

private structure NormStepInput where
  goal : MVarId
  depth : Nat
  enableSimp : Bool
  goalMVars : Std.HashSet MVarId
  /- Whether to reconstruct surface tactics for `iaesop?` script generation.
  Disabled during search to avoid building syntax that is thrown away. -/
  recordScript : Bool := false

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
    (pat : iCasesPat) : ProofModeM (Option (MVarId × Name)) := do
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
      return (← newGoalRef.get).map (·, info.name)
  catch _ =>
    set prePMState
    liftM <| preState.restore
    return none

private def firstSuccessfulCasesStep (goal : MVarId)
    (infos : Array IrisHypInfo)
    (pat : iCasesPat)
    (eligible : IrisHypInfo → MetaM Bool) :
    ProofModeM (Option (MVarId × Name)) := do
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

private def canExists {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)}
    (info : IrisHypInfo) : MetaM Bool := do
  let ty ← instantiateMVars info.ty
  let some irisTy ← checkTypeQ ty prop | return false
  let v ← mkFreshLevelMVar
  let α : Q(Sort v) ← mkFreshExprMVarQ q(Sort v)
  let Φ : Q($α → $prop) ← mkFreshExprMVarQ q($α → $prop)
  match ← ProofMode.trySynthInstanceQ q(IntoExists $irisTy $Φ) with
  | .some _ => return true
  | _ => return false

private def canSplitSep (info : IrisHypInfo) : MetaM Bool := do
  let ty ← instantiateMVars info.ty
  let target := ty.consumeMData
  if target.getAppFn.constName? == some ``BIBase.sep then
    match target.getAppArgs.toList.reverse with
    | _ :: _ :: _ => return true
    | _ => return false
  return false

private def canSplitConjLike {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)}
    (info : IrisHypInfo) : MetaM Bool := do
  let ty : Q($prop) ← instantiateMVars info.ty
  let some p ← checkTypeQ info.p q(Bool) | return false
  let lhs ← mkFreshExprMVarQ prop
  let rhs ← mkFreshExprMVarQ prop
  match matchBool p with
  | .inl _ => match ← ProofMode.trySynthInstanceQ q(IntoAnd $p $ty $lhs $rhs) with
    | .some _ => return true
    | _ => return false
  | .inr _ => return false

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
      let tac? ← if input.recordScript then
        liftM <| some <$> mkIntroTactic (.intro (.pure pureName))
      else pure none
      return .changed newGoal tac?
    let name ← mkFreshBinderFromNames names input.depth
    if let some newGoal ← runIntroPat input.goal (.intro (.one name)) then
      let tac? ← if input.recordScript then
        liftM <| some <$> mkIntroTactic (.intro (.one name))
      else pure none
      return .changed newGoal tac?
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

      /- Split Spatial separating conjunctions first -/
      let h₁ ← mkFreshBinderFromNames names input.depth
      let h₂ ← mkFreshBinderFromNames names input.depth 2
      let sepPat := iCasesPat.conjunction [.one h₁, .one h₂]
      if let some (newGoal, hyp) ←
          firstSuccessfulCasesStep input.goal infos sepPat canSplitSep then
        return .changed newGoal (← liftM <| mkICasesTactic? input.recordScript hyp sepPat)

       /- Destruct existentials: `icases H with ⟨%x, Hx⟩`. -/
      let x ← mkFreshLeanBinderFromNames names input.depth
      let h ← mkFreshBinderFromNames names input.depth
      let exPat := iCasesPat.conjunction [.pure x, .one h]
      if let some (newGoal, hyp) ←
          firstSuccessfulCasesStep input.goal infos exPat
            (canExists (prop := irisGoal.prop) (bi := irisGoal.bi)) then
        return .changed newGoal (← liftM <| mkICasesTactic? input.recordScript hyp exPat)

      /- Split conjunction-like hypotheses, including iff -/
      let h₁ ← mkFreshBinderFromNames names input.depth
      let h₂ ← mkFreshBinderFromNames names input.depth 2
      let conjPat := iCasesPat.conjunction [.one h₁, .one h₂]
      if let some (newGoal, hyp) ←
          firstSuccessfulCasesStep input.goal infos conjPat
            (canSplitConjLike (prop := irisGoal.prop) (bi := irisGoal.bi)) then
        return .changed newGoal (← liftM <| mkICasesTactic? input.recordScript hyp conjPat)

      /- Extract pure hypotheses. -/
      let h ← mkFreshBinderFromNames names input.depth
      let purePat := iCasesPat.pure h
      if let some (newGoal, hyp) ←
          firstSuccessfulCasesStep input.goal infos purePat
            (canPure (prop := irisGoal.prop) (bi := irisGoal.bi)) then
        return .changed newGoal (← liftM <| mkICasesTactic? input.recordScript hyp purePat)
      /- Move persistent hypotheses into the intuitionistic context -/
      let h ← mkFreshBinderFromNames names input.depth
      let intuitPat := iCasesPat.intuitionistic (.one h)
      match ←
          firstSuccessfulCasesStep input.goal infos intuitPat
            (canIntuitionistic (prop := irisGoal.prop) (bi := irisGoal.bi)) with
      | some (newGoal, hyp) =>
          return .changed newGoal (← liftM <| mkICasesTactic? input.recordScript hyp intuitPat)
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
            return .changed newGoal none
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
    (maxIterations : Nat) (enableSimp : Bool) (goalMVars : Std.HashSet MVarId)
    (recordScript : Bool := false) :
    ProofModeM (NormSeqResult × Array Script.LazyStep) := do
  go 0 goal false #[]
where
  go (iteration : Nat) (goal : MVarId) (changed : Bool)
      (script : Array Script.LazyStep) :
      ProofModeM (NormSeqResult × Array Script.LazyStep) := do
    if iteration >= maxIterations then
      throwError "iaesop: exceeded maximum number of normalisation iterations ({maxIterations})."
    let input : NormStepInput := { goal, depth, enableSimp, goalMVars, recordScript }
    /- Only snapshot states when generating a script; search throws them away. -/
    let preState? ← if recordScript then
        liftM (m := MetaM) (some <$> saveState) else pure none
    match ← runFirstNormStep input with
    | .proved => return (.proved, script)
    | .changed newGoal tactic? =>
      let script ← match tactic?, preState? with
        | some tactic, some preState =>
          let postState ← liftM (m := MetaM) saveState
          pure <| script.push
            { preState, preGoal := goal, tactic, postState, postGoals := #[newGoal] }
        | _, _ => pure script
      go (iteration + 1) newGoal true script
    | .unchanged =>
      if changed then return (.changed goal, script)
      else return (.unchanged, script)

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
        return (spatialHypEntries irisGoal.hyps).map λ (name, ivar, _) => { name, ivar }

      let (result, _) ← normalizeGoalMVar preGoalMVarId goal.depth
          config.maxNormIterations config.enableSimp? goal.unassignedMvars

      /- Collect spatial hypotheses after normalization. -/
      let postHyps : Array IrisHyp ← match result with
        | .proved => pure #[]
        | .unchanged => pure preHyps
        | .changed postGoal => liftM (m := MetaM) <| postGoal.withContext do
          let goalType ← instantiateMVars (← postGoal.getType)
          let some irisGoal := parseIrisGoal? goalType
            | throwError "iaesop: normalization stage should be done in iris proof-mode"
          return (spatialHypEntries irisGoal.hyps).map λ (name, ivar, _) => { name, ivar }

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
