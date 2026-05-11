module

public meta import Iris.ProofMode.Aesop.Search.SearchM
public meta import Iris.ProofMode.Aesop.Search.Expansion
public meta import Iris.ProofMode.Tactics.Assumption
public meta import Iris.ProofMode.Tactics.Split

public meta section

namespace Iris.ProofMode.Aesop.Search

open Lean Elab Tactic Meta Qq Std
open Iris.ProofMode
open Iris.BI

variable {Q : Type} [Queue Q]

private partial def splitSep? (target : Expr) : Option (Expr × Expr) :=
  let target := target.consumeMData
  if target.getAppFn.constName? == some ``BIBase.sep then
    match target.getAppArgs.toList.reverse with
    | rhs :: lhs :: _ => some (lhs, rhs)
    | _ => none
  else
    none

private partial def sepLeafCount (target : Expr) : Nat :=
  match splitSep? target with
  | some (lhs, rhs) => sepLeafCount lhs + sepLeafCount rhs
  | none => 1

private structure LeafProofInfo where
  target : Expr
  used : UsedIrisHyp
  deriving Inhabited

private def mkAssumptionProof
    {prop : Q(Type u)} {bi : Q(BI $prop)} {e}
    (hyps : Hyps bi e) (target : Q($prop)) (used : UsedIrisHyp) :
    MetaM (Option Q($e ⊢ $target)) := do
  unless used.spatial do
    return none
  if !hyps.spatialIVarIds.contains used.ivar then
    return none
  let ⟨e', _, _, out, p, _, pf⟩ := hyps.remove false used.ivar
  let .some (inst, _) ← ProofMode.trySynthInstanceQ
      q(FromAssumption $p .in $out $target)
    | return none
  let _ : Q(FromAssumption $p .in $out $target) := inst
  let .some _ ← trySynthInstanceQ q(TCOr (Affine $e') (Absorbing $target))
    | return none
  return some q(Iris.ProofMode.assumption (Q := $target) $pf)

private partial def mkManagedProof
    {prop : Q(Type u)} {bi : Q(BI $prop)} {e}
    (hyps : Hyps bi e) (target : Q($prop))
    (leaves : Array LeafProofInfo) :
    MetaM (Option Q($e ⊢ $target)) := do
  match splitSep? target with
  | none =>
    if leaves.size == 1 then
      mkAssumptionProof hyps target leaves[0]!.used
    else
      return none
  | some (lhsExpr, rhsExpr) =>
    let lhs : Q($prop) := Qq.Quoted.unsafeMk lhsExpr
    let rhs : Q($prop) := Qq.Quoted.unsafeMk rhsExpr
    let lhsLeafCount := sepLeafCount lhs
    if lhsLeafCount == 0 || leaves.size < lhsLeafCount then
      return none
    let lhsLeaves := leaves.extract 0 lhsLeafCount
    let rhsLeaves := leaves.extract lhsLeafCount leaves.size
    let ⟨_, _, lhsHyps, rhsHyps, pf⟩ :=
      Hyps.split bi
        (λ _ ivar => rhsLeaves.any (λ leaf => leaf.used.ivar == ivar))
        hyps
    let some lhsPf ← mkManagedProof lhsHyps lhs lhsLeaves
      | return none
    let some rhsPf ← mkManagedProof rhsHyps rhs rhsLeaves
      | return none
    let fromSepType ← mkAppM ``FromSep #[target, lhs, rhs]
    let .some _ ← ProofMode.trySynthInstance fromSepType
      | return none
    let proof ← mkAppOptM ``Iris.ProofMode.sep_split #[
      none, none, none, none, none, some target, some lhs, some rhs,
      none, some pf, some lhsPf, some rhsPf
    ]
    return some (Qq.Quoted.unsafeMk proof)

private def collectManagedLeafProofs (rapp : Rapp) (obun : Obun) :
    SearchM Q (Option (Array LeafProofInfo)) := do
  if obun.goals.size != rapp.irisSubgoals.size then
    return none
  let mut leaves := #[]
  for (gref, irisGoal) in obun.goals.zip rapp.irisSubgoals do
    let g ← gref.get
    unless g.state.isProven do
      return none
    let some used := g.usedIrisHyp?
      | return none
    leaves := leaves.push { target := irisGoal.goal, used }
  return some leaves

private def finalizeManagedObunProof (obunRef : ObunRef) : SearchM Q Bool := do
  let obun ← obunRef.get
  if !obun.kind.isManaged then
    return true
  let some rappRef := obun.parent?
    | return true
  let rapp ← rappRef.get
  let some leaves ← collectManagedLeafProofs rapp obun
    | return false
  let parent ← rapp.parent.get
  let some parentGoal := parent.normalizationState.normalizedGoal?
    | return false
  let state := obun.metaState?.getD rapp.metaState
  let ok ← liftM do
    restoreState state
    parentGoal.withContext do
      let goalType ← instantiateMVars (← parentGoal.getType)
      let some irisGoal := parseIrisGoal? goalType
        | return false
      let some pf ← mkManagedProof irisGoal.hyps irisGoal.goal leaves
        | return false
      parentGoal.assign pf
      return true
  if ok then
    dbg_trace s!"finalized managed obun {obun.id} proof"
  return ok

private def allGoalsProven (goals : Array GoalRef) : SearchM Q Bool := do
  for gref in goals do
    if !(← gref.get).state.isProven then
      return false
  return true

private def anyObunProven (obuns : Array ObunRef) : SearchM Q Bool := do
  for oref in obuns do
    if (← oref.get).state.isProven then
      return true
  return false

private meta partial def propagateProvenFromGoal (gref : GoalRef) : SearchM Q Unit := do
  let g ← gref.get
  unless g.state.isProven do
    return
  let obunRef := g.parent
  let obun ← obunRef.get
  if obun.state.isProven then
    return
  unless ← allGoalsProven obun.goals do
    return
  unless ← finalizeManagedObunProof obunRef do
    dbg_trace s!"could not finalize obun {obun.id} yet"
    return
  obunRef.modify λ o => o.setState .proven
  match obun.parent? with
  | none => return
  | some rappRef =>
    let rapp ← rappRef.get
    if rapp.state.isProven then
      return
    unless ← anyObunProven rapp.children do
      return
    rappRef.modify λ r => r.setState .proven
    let parentRef := rapp.parent
    parentRef.modify λ g => g.setState .provenByRuleApplication
    propagateProvenFromGoal parentRef

private meta partial def nextActiveGoal? : SearchM Q (Option GoalRef) := do
  let some gref ← popGoal?
    | return none
  if (← (← gref.get).isActive) then
    return some gref
  else nextActiveGoal?

private meta def expandNextGoal : SearchM Q Bool := do
  let some gref ← nextActiveGoal?
    | return false
  let result ← expandGoal gref
  let currentIteration ← getIteration
  gref.modify λ g => g.setLastExpandedInIteration currentIteration
  if ← (← gref.get).isActive then enqueueGoals #[gref]
  match result with
  | .failed => pure ()
  | .proved newRapps | .succeeded newRapps =>
    for rref in newRapps do
      -- [Note]: Trace some information here about new generated Rapps
      let _ ← rref.get
  if (← gref.get).state.isProven then
    propagateProvenFromGoal gref
  return true

private meta def Goal.currentMVar? (g : Goal) : Option MVarId :=
  if g.state.isProven then
    none
  else
    match g.normalizationState with
    | .notNormal => some g.preNormGoal
    | .normal postGoal .. => some postGoal
    | .provenByNorm .. => none

private meta def collectRemainingGoals : SearchM Q (Array MVarId) := do
  let queuedGoals ← Queue.toArray (← getThe (SearchM.State Q)).queue
  let refs ←
    if queuedGoals.isEmpty then
      pure #[← getRootGoal]
    else
      pure queuedGoals
  refs.foldlM (init := #[]) λ goals gref => do
    let g ← gref.get
    return goals ++ (Goal.currentMVar? g).toArray

private meta def finalizeProof : SearchM Q Unit := do
  (← getRootMVar).withContext do
    return

/-- Check tree status function set -/
private meta def checkRootProven : SearchM Q Bool := do
  if (← (← getRootGoal).get).state.isProven then
    finalizeProof
    return true
  else
    return false

private meta def checkRootUnprovable : SearchM Q (Option MessageData) := do
  return none

private meta def checkGoalLimit : SearchM Q (Option MessageData) := do
  return none

private meta def checkRappLimit : SearchM Q (Option MessageData) := do
  return none

private meta def checkNonfatalError? : SearchM Q (Option MessageData) := do
  let checks : Array (SearchM Q (Option MessageData)) :=
    #[checkRootUnprovable, checkGoalLimit, checkRappLimit]
  for check in checks do
    if let some err ← check then
      return some err
  return none

private meta def handleNonfatalError (_err : MessageData) : SearchM Q (Array MVarId) := do
  return #[]

-- Main Search loop
private meta partial def searchLoop : SearchM Q (Array MVarId) :=
  withIncRecDepth do
    checkSystem "iaesop"
    if ← checkRootProven then return #[]
    if let some err ← checkNonfatalError? then
      handleNonfatalError err
    else
      if ← expandNextGoal then
        incrementIteration
        searchLoop
      else
        collectRemainingGoals

meta def search (goal : MVarId) (_irisGoal : IrisGoal) (config : SearchConfig := {}) :
    ProofModeM (Array MVarId) := do
  goal.checkNotAssigned `iaesop
  -- TODO: parse ruleset before run search loop
  -- Currently, we only work on the hypothesis in the Hyps
  -- TODO: extend this to support multiple strategy (can parse Q from configuration)
  let (remaining, _, _) ← SearchM.run (Q := BestFirstQueue) config goal do
    searchLoop
  return remaining

end Search
