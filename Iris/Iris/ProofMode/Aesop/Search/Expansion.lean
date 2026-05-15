module

public meta import Iris.ProofMode.Aesop.Search.SearchM
public meta import Iris.ProofMode.Aesop.Search.Types
public meta import Iris.ProofMode.Aesop.Search.Normalization
public meta import Iris.ProofMode.Aesop.Search.RuleSelection
public meta import Iris.ProofMode.Tactics.Assumption

public meta section

namespace Iris.ProofMode.Aesop

open Lean Tactic Meta Qq Std
open Iris.ProofMode
open Iris.BI

variable {Q : Type} [Queue Q]

private partial def splitSepTargets (target : Expr) : Array Expr :=
  let target := target.consumeMData
  if target.getAppFn.constName? == some ``BIBase.sep then
    match target.getAppArgs.toList.reverse with
    | rhs :: lhs :: _ => splitSepTargets lhs ++ splitSepTargets rhs
    | _ => #[target]
  else
    #[target]

private structure SplitChild where
  goal : MVarId
  irisGoal : IrisGoal
  mvars : Std.HashSet MVarId

private structure ApplyHypCandidate where
  hyp : IrisHyp
  premises : Array Expr
  deriving Inhabited

private structure IExactResult where
  used : Array UsedIrisHyp
  postState : SavedState

private def wandParts? (target : Expr) : Option (Expr × Expr) :=
  let target := target.consumeMData
  if target.getAppFn.constName? == some ``BIBase.wand then
    match target.getAppArgs.toList.reverse with
    | rhs :: lhs :: _ => some (lhs, rhs)
    | _ => none
  else
    none

private partial def collectWandPremises?
    (hypType : Expr) (target : Expr) : MetaM (Option (Array Expr)) := do
  let hypType ← instantiateMVars hypType
  let target ← instantiateMVars target
  if ← isDefEq hypType target then
    return some #[]
  match wandParts? hypType with
  | none => return none
  | some (premise, rest) =>
    let some premises ← collectWandPremises? rest target
      | return none
    return some (#[premise] ++ premises)

private partial def collectApplyHypCandidates {u prop bi} (target : Expr) :
    ∀ {e}, @Hyps u prop bi e → MetaM (Array ApplyHypCandidate)
  | _, .emp _ => return #[]
  | _, .hyp _ name ivar _ ty _ => do
    let some premises ← collectWandPremises? ty target
      | return #[]
    if premises.isEmpty then
      return #[]
    return #[{ hyp := { name, ivar }, premises }]
  | _, .sep _ _ _ _ lhs rhs => do
    return (← collectApplyHypCandidates target lhs) ++
      (← collectApplyHypCandidates target rhs)

private def mkSplitChildren (goal : MVarId) : MetaM (Option (Array SplitChild)) := do
  goal.withContext do
    let goalType ← instantiateMVars (← goal.getType)
    let some irisGoal := parseIrisGoal? goalType
      | return none
    let target ← instantiateMVars irisGoal.goal
    let targets := splitSepTargets target
    if targets.size <= 1 then
      return none
    let tag ← goal.getTag
    some <$> targets.mapM λ target => do
      let irisGoal := { irisGoal with goal := target }
      let goalExpr ← mkFreshExprSyntheticOpaqueMVar (IrisGoal.toExpr irisGoal) tag
      let goal := goalExpr.mvarId!
      return {
        goal
        irisGoal
        mvars := ← goal.getMVarDependencies
      }

private def runIdentityRule (parentRef : GoalRef) (matchResult : RuleMatch) :
    SearchM Q RuleResult := do
  let parent ← parentRef.get

  let (goal, state) ← match parent.normalizationState with
    | .normal postGoal postState .. =>
      pure (postGoal, postState)
    | .provenByNorm .. =>
      throwError "iaesop: internal error: identity rule ran on a goal already proven by normalization"
    | .notNormal =>
      throwError "iaesop: internal error: identity rule ran on a non-normalized goal"

  let (some children, postState) ← liftM do
      restoreState state
      let children? ← mkSplitChildren goal
      let postState ← saveState
      return (children?, postState)
    | return .failed

  dbg_trace s!"identity split target into {children.size} goals"
  for child in children do
    let targetFmt ← liftM <| ppExpr child.irisGoal.goal
    dbg_trace s!"  identity child target: {targetFmt.pretty}"

  let obunRef ← IO.mkRef $ Obun.mk {
    id := ← getAndIncrementNextObunId
    parent? := none
    goals := #[]
    state := .unknown
    isIrrelevant := false
    kind := .managed
    scriptSteps? := none
    metaState? := some postState
  }
  let rappRef ← IO.mkRef $ Rapp.mk {
    id := ← getAndIncrementNextRappId
    parent := parentRef
    children := obunRef
    state := .unknown
    isIrrelevant := false
    appliedRule := matchResult.rule.payload
    successProbability := parent.successProbability * matchResult.rule.payload.successProbability
    scriptSteps? := none
    fullContextIrisSubgoals := children.map (·.irisGoal)
    consumedSpatialHyp? := none
    finalizedSpatialSplits := children.map (λ _ => #[])
    metaState := postState
    introducedMVars := {}
    assignedMVars := {}
  }
  let currentIteration ← getIteration
  let goalRefs ← children.mapIdxM λ i child => do
    IO.mkRef $ Goal.mk {
      id := ← getAndIncrementNextGoalId
      mask := (ProgressMask.empty children.size).mark i
      parent := obunRef
      children := #[]
      origin := .subgoal
      depth := parent.depth + 1
      state := .unknown
      isIrrelevant := false
      isForcedUnprovable := false
      preNormGoal := child.goal
      preNormState := postState
      normalizationState := .notNormal
      unassignedMvars := child.mvars
      successProbability := parent.successProbability * matchResult.rule.payload.successProbability
      addedInIteration := currentIteration
      lastExpandedInIteration := currentIteration
      rulesQueue := {}
      appendiedGoalId := #[]
    }

  obunRef.modify λ o => (o.setParent rappRef).setGoals goalRefs
  parentRef.modify λ g => g.setChildren (g.children.push rappRef)
  enqueueGoals goalRefs
  return .succeeded #[rappRef]

private def mkApplyHypChildren (goal : MVarId) :
    MetaM (Option (Array (ApplyHypCandidate × Array SplitChild))) := do
  goal.withContext do
    let goalType ← instantiateMVars (← goal.getType)
    let some irisGoal := parseIrisGoal? goalType
      | return none
    let target ← instantiateMVars irisGoal.goal
    let candidates ← collectApplyHypCandidates target irisGoal.hyps
    if candidates.isEmpty then
      return none
    let tag ← goal.getTag
    some <$> candidates.mapM λ candidate => do
      let some ⟨_, e', hyps', _, _, _, _, _⟩ ←
          irisGoal.hyps.removeG true fun _ ivar _ _ => do
            if ivar == candidate.hyp.ivar then return some ()
            else return none
        | throwError "iaesop: internal error: applyHyps candidate disappeared"
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

private def runApplyHypsRule (parentRef : GoalRef) (matchResult : RuleMatch) :
    SearchM Q RuleResult := do
  let parent ← parentRef.get
  let (goal, state) ← match parent.normalizationState with
    | .normal postGoal postState .. =>
      pure (postGoal, postState)
    | .provenByNorm .. =>
      throwError "iaesop: internal error: applyHyps ran on a goal already proven by normalization"
    | .notNormal =>
      throwError "iaesop: internal error: applyHyps ran on a non-normalized goal"

  let (some expansions, postState) ← liftM do
      restoreState state
      let children? ← mkApplyHypChildren goal
      let postState ← saveState
      return (children?, postState)
    | return .failed

  let currentIteration ← getIteration
  let mut rappRefs := #[]
  let mut goalRefsToEnqueue := #[]
  for (candidate, children) in expansions do
    dbg_trace s!"applyHyps selected {candidate.hyp.name} and generated {children.size} goals"
    for child in children do
      let targetFmt ← liftM <| ppExpr child.irisGoal.goal
      dbg_trace s!"  applyHyps child target: {targetFmt.pretty}"

    let obunRef ← IO.mkRef $ Obun.mk {
      id := ← getAndIncrementNextObunId
      parent? := none
      goals := #[]
      state := .unknown
      isIrrelevant := false
      kind := .managed
      scriptSteps? := none
      metaState? := some postState
    }
    let rappRef ← IO.mkRef $ Rapp.mk {
      id := ← getAndIncrementNextRappId
      parent := parentRef
      children := obunRef
      state := .unknown
      isIrrelevant := false
      appliedRule := matchResult.rule.payload
      successProbability := parent.successProbability * matchResult.rule.payload.successProbability
      scriptSteps? := none
      fullContextIrisSubgoals := children.map (·.irisGoal)
      consumedSpatialHyp? := some candidate.hyp
      finalizedSpatialSplits := children.map (λ _ => #[])
      metaState := postState
      introducedMVars := {}
      assignedMVars := {}
    }
    let goalRefs ← children.mapIdxM λ i child => do
      IO.mkRef $ Goal.mk {
        id := ← getAndIncrementNextGoalId
        mask := (ProgressMask.empty children.size).mark i
        parent := obunRef
        children := #[]
        origin := .subgoal
        depth := parent.depth + 1
        state := .unknown
        isIrrelevant := false
        isForcedUnprovable := false
        preNormGoal := child.goal
        preNormState := postState
        normalizationState := .notNormal
        unassignedMvars := child.mvars
        successProbability := parent.successProbability * matchResult.rule.payload.successProbability
        addedInIteration := currentIteration
        lastExpandedInIteration := currentIteration
        rulesQueue := {}
        appendiedGoalId := #[]
      }
    obunRef.modify λ o => (o.setParent rappRef).setGoals goalRefs
    rappRefs := rappRefs.push rappRef
    goalRefsToEnqueue := goalRefsToEnqueue ++ goalRefs

  parentRef.modify λ g => g.setChildren (g.children ++ rappRefs)
  enqueueGoals goalRefsToEnqueue
  return .succeeded rappRefs

partial def findManagedObun? (gref : GoalRef) : SearchM Q (Option ObunRef) := do
  let g ← gref.get
  let obunRef := g.parent
  let obun ← obunRef.get
  if obun.kind.isManaged && obun.state.isUnknown then
    return some obunRef
  else
    match obun.parent? with
    | none => return none
    | some rappRef =>
      findManagedObun? (← rappRef.get).parent

private def runIExactRule (parentRef : GoalRef) (matchResult : RuleMatch) :
  SearchM Q RuleResult := do
  let parent ← parentRef.get
  let some goal := parent.normalizationState.normalizedGoal?
    | return .failed
  let normState :=
    match parent.normalizationState with
    | .normal _ postState .. => postState
    | _ => parent.preNormState
  let managedObun? ← findManagedObun? parentRef
  let isManaged := managedObun?.isSome
  let mut state := normState
  if let some obunRef := managedObun? then
    let obun ← obunRef.get
    state := obun.metaState?.getD normState
  let result? : Option IExactResult ← liftM do
      restoreState state
      goal.withContext do
        let goalType ← instantiateMVars (← goal.getType)
        let some { hyps, goal := target, .. } := parseIrisGoal? goalType
          | return none
        let some ⟨(inst, used), e', _, out, ty, b, _, pf⟩ ←
            hyps.removeG true fun name ivar b ty => do
              let .some (inst, _) ← ProofMode.trySynthInstanceQ
                  q(FromAssumption $b .in $ty $target)
                | return none
              let used : Array UsedIrisHyp :=
                if isTrue b then
                  #[]
                else
                  #[{ name, ivar }]
              return some (inst, used)
          | return none
        let _ : Q(FromAssumption $b .in $ty $target) := inst
        have : $out =Q iprop(□?$b $ty) := ⟨⟩
        match ← trySynthInstanceQ q(TCOr (Affine $e') (Absorbing $target)) with
        | .some _ =>
          goal.assign q(Iris.ProofMode.assumption (Q := $target) $pf)
        | _ =>
          unless isManaged do
            return none
          dbg_trace s!"iexact accepted in managed context; ordinary proof assignment is deferred"
        let postState ← saveState
        let result : IExactResult := { used, postState }
        return some result
  let some result := result?
    | return .failed
  let obunRef ← IO.mkRef $ Obun.mk {
    id := ← getAndIncrementNextObunId
    parent? := none
    goals := #[]
    state := .proven
    isIrrelevant := false
    metaState? := some result.postState
    scriptSteps? := none
    kind := .plain
  }
  let rappRef ← IO.mkRef $ Rapp.mk {
    id := ← getAndIncrementNextRappId
    parent := parentRef
    children := obunRef
    state := .proven
    isIrrelevant := false
    appliedRule := matchResult.rule.payload
    successProbability := parent.successProbability * matchResult.rule.payload.successProbability
    scriptSteps? := none
    fullContextIrisSubgoals := #[]
    consumedSpatialHyp? := result.used[0]?
    finalizedSpatialSplits := #[]
    metaState := result.postState
    introducedMVars := {}
    assignedMVars := {}
  }
  obunRef.modify λ o => o.setParent rappRef
  parentRef.modify λ g =>
    (g.setChildren (g.children.push rappRef)).setState
      (.provenByRuleApplication result.used)
  if let some obunRef := managedObun? then
    obunRef.modify λ o => o.setMetaState? (some result.postState)
  return .proved #[rappRef]

private def runRule (parentRef : GoalRef) (matchResult : RuleMatch) :
    SearchM Q RuleResult := do
  -- [Note] only two unindex rules registered
  if matchResult.rule.id == identityRuleId then
    runIdentityRule parentRef matchResult
  else if matchResult.rule.id == iexactRuleId then
    runIExactRule parentRef matchResult
  else if matchResult.rule.id == applyHypsRuleId then
    runApplyHypsRule parentRef matchResult
  else
    return .failed

private partial def runFirstRule (parentRef : GoalRef) : SearchM Q RuleResult := do
  let ruleCandidates ← selectRules parentRef
  let (remainingRules, result) ← pickLoop ruleCandidates
  parentRef.modify λ g => g.setRulesQueue remainingRules
  -- [Note] dropped the "mark unprovable" here, we can postpone it until
  -- Search Main loop (I suppose)
  return result
  where
    pickLoop (queue : RuleQueue) : SearchM Q (RuleQueue × RuleResult) := do
      let some (matchResult, queue) := RuleQueue.pop? queue
        | return (queue, .failed)
      let result ← runRule parentRef matchResult
      match result with
      | .proved .. | .succeeded .. => return (queue, result)
      | .failed => pickLoop queue

def expandGoal (gref : GoalRef) : SearchM Q RuleResult := do
  if !(← (← gref.get).isNormalized) then normalizeGoal gref
  if (← gref.get).normalizationState.isProvenByNorm then
    return .proved #[]

  -- run first rule that selected and return back result
  runFirstRule gref

end Aesop
