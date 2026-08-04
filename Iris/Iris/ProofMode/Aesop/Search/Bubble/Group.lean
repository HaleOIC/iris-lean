module

public meta import Iris.ProofMode.Aesop.Search.Bubble.Meta
public meta import Iris.ProofMode.Aesop.Search.Shared.Names

public meta section

namespace Iris.ProofMode.Aesop.Search.Bubble

open Lean Meta Std
open Iris.ProofMode
open Iris.ProofMode.Aesop

variable {Q : Type} [Queue Q]

-- Helper function
private def sameResource (a b : IrisHyp) : Bool :=
  a.ivar == b.ivar

private def appendResources (policy : ResourcePolicy)
    (xs ys : Array IrisHyp) : Option (Array IrisHyp) :=
  if policy == .disjoint && !xs.all (fun x => !ys.any (sameResource x)) then
    none
  else
    some <| ys.foldl (init := xs) fun acc resource =>
      if acc.any (sameResource resource) then acc else acc.push resource

private def resourcesConflict (left right : Array IrisHyp) : Bool :=
  left.any fun resource => right.any (sameResource resource)

private def removeConsumedResources (goal : IrisGoal) (consumed : Array IrisHyp) :
    MetaM IrisGoal :=
  consumed.foldlM (init := goal) fun goal used => do
    if !goal.hyps.spatialIVarIds.contains used.ivar then return goal
    let ⟨e, hyps, _, _, _, _, _⟩ := goal.hyps.remove false used.ivar
    return { goal with e, hyps }

private def sharesDependency [BEq α] (left right : Array α) : Bool :=
  left.any right.contains

/- Connected components, not equality classes: a transitive bridge through a
third goal keeps all three goals in one dependency group. -/
def dependencyComponents [BEq α] (dependencies : Array (Array α)) :
    Array (Array Nat) := Id.run do
  let mut components : Array (Array Nat) := #[]
  for index in List.range dependencies.size do
    let touching := components.filter fun component =>
      component.any fun member =>
        sharesDependency dependencies[index]! dependencies[member]!
    let untouched := components.filter fun component =>
      !component.any fun member =>
        sharesDependency dependencies[index]! dependencies[member]!
    let merged := touching.foldl (init := #[index]) fun acc component =>
      acc ++ component
    components := untouched.push merged
  return components

private def registerGroup (obunRef : ObunRef) (group : GoalGroup) : BubbleM Q Unit :=
  setGroup obunRef group

private def enqueueGroup (group : GoalGroup) : BubbleM Q Unit :=
  liftM (m := Iris.ProofMode.Aesop.CoreM Q) <|
    enqueueGoals (group.members.map (fun member => member.goal))

def registerInitialGroups (rappRef : RappRef) (goalRefs : Array GoalRef) :
    BubbleM Q Unit := do
  let rapp ← rappRef.get
  let obun ← rapp.children.get
  let dependencies ← goalRefs.mapM fun goalRef => do
    return (← goalRef.get).unassignedMvars.toArray
  let roots := dependencyComponents dependencies
  let policy := if obun.kind.isManaged then .disjoint else .shared
  rapp.children.modify fun current =>
    (current.setBubbleDependencyRoots roots).setBubblePlatform?
      (some (Platform.empty roots.size policy))
  registerPlatformObun rapp.children
  for rootIndex in List.range roots.size do
    let indices := roots[rootIndex]!
    let members ← indices.mapM fun originalIndex => do
      let some goal := goalRefs[originalIndex]?
        | throwError "iaesop(bubble): dependency group index is out of bounds"
      return { originalIndex, goal }
    let group : GoalGroup := {
      id := ← freshGroupId
      rootIndex
      members
      platform := Platform.empty members.size policy
    }
    registerGroup rapp.children group
    enqueueGroup group
    trace[iaesop.search.bubble] "iaesop(bubble): created root group {group.id} for \
      obun {obun.id}; root={rootIndex}; members={indices}"

private def findGroupLocations (obun : Obun) (goalId : GoalId) :
    BubbleM Q (Array GoalGroupLocation) := do
  let mut locations := #[]
  for group in obun.bubbleGroups do
    for memberIndex in List.range group.members.size do
      let some member := group.members[memberIndex]?
        | throwError "iaesop(bubble): group member index is out of bounds"
      if (← member.goal.get).id == goalId then
        locations := locations.push { goalId, groupId := group.id, memberIndex }
  if locations.isEmpty then
    throwError "iaesop(bubble): goal {goalId} is not registered in an Obun group"
  return locations

private def groupResidualAlreadySpawned (obunId : ObunId) (rootIndex : Nat)
    (trigger : BubbleId) (preGroup : GroupId) : BubbleM Q Bool :=
  return (← getThe State).spawnedGroups.any fun entry =>
    entry.obunId == obunId && entry.rootIndex == rootIndex &&
      entry.trigger == trigger && entry.preGroup == preGroup

private def markResidualSpawned (obunId : ObunId) (rootIndex : Nat)
    (trigger : BubbleId) (preGroup : GroupId) : BubbleM Q Unit :=
  modifyThe State fun state => {
    state with
    spawnedGroups := state.spawnedGroups.push { obunId, rootIndex, trigger, preGroup }
  }

private def originalTemplate (obun : Obun) (originalIndex : Nat)
    (original : Goal) : MetaM IrisGoal := do
  match obun.fullContextIrisSubgoals[originalIndex]? with
  | some template => pure template
  | none =>
    let type ← instantiateMVars (← original.preNormGoal.getType)
    let some template := parseIrisGoal? type
      | throwError "iaesop(bubble): grouped residual expected an Iris goal"
    return template

private def mkResidualGroup (obunRef : ObunRef) (rootIndex : Nat)
    (indices : Array Nat) (prefixProofs : Array (Nat × BubbleId))
    (prefixConsumed : Array IrisHyp) (prefixMetaInfo : Array MetaAssignment)
    (externalPrefix? : Option BubbleId) (externalAncestors : Array BubbleId)
    (externalConsumed : Array IrisHyp) (externalMetaInfo : Array MetaAssignment)
    (trigger : BubbleId) (preGroup : GroupId) (preBubble : BubbleId) : BubbleM Q Bool := do
  let obun ← obunRef.get
  if indices.isEmpty ||
      (← groupResidualAlreadySpawned obun.id rootIndex trigger preGroup) then return false
  let some parentRappRef := obun.parent? | return false
  let parentRapp ← parentRappRef.get
  let allMeta := externalMetaInfo ++ prefixMetaInfo
  let some refinedState ← applyMetaInfo parentRapp.metaState allMeta | return false
  let allConsumed := externalConsumed ++ prefixConsumed
  let mut members : Array GroupMember := #[]
  for originalIndex in indices do
    let some originalRef := obun.goals[originalIndex]?
      | throwError "iaesop(bubble): residual group member index is out of bounds"
    let original ← originalRef.get
    let (goalMVar, postState, mvars) ←
      liftM (m := Iris.ProofMode.Aesop.CoreM Q) <| liftM (m := MetaM) <|
        refinedState.runMetaM' do
          original.preNormGoal.withContext do
            let template ← originalTemplate obun originalIndex original
            let template ←
              if obun.kind.isManaged then removeConsumedResources template allConsumed
              else pure template
            let type ← instantiateMVars (IrisGoal.toExpr template)
            let tag ← original.preNormGoal.getTag
            let goalMVar := (← mkFreshExprSyntheticOpaqueMVar type tag).mvarId!
            return (goalMVar, ← saveState, ← goalMVar.getMVarDependencies)
    let goalId ← liftM (m := Iris.ProofMode.Aesop.CoreM Q) getAndIncrementNextGoalId
    let iteration ← liftM (m := Iris.ProofMode.Aesop.CoreM Q) getIteration
    let goalRef ← IO.mkRef <| Goal.mk {
      id := goalId
      mask := (ProgressMask.empty obun.goals.size).mark originalIndex
      parent := obunRef
      children := #[]
      origin := .subgoal
      depth := original.depth
      state := .unknown
      isIrrelevant := false
      isForcedUnprovable := false
      preNormGoal := goalMVar
      preNormState := postState
      normalizationState := .notNormal
      unassignedMvars := mvars
      successProbability := original.successProbability
      addedInIteration := iteration
      lastExpandedInIteration := .zero
      rulesQueue := {}
      appendiedGoalId := #[]
      caseId? := some (CaseId.ofNat originalIndex)
    }
    recordResidual { goalId, obunId := obun.id, childIndex := originalIndex, pre := preBubble }
    members := members.push { originalIndex, goal := goalRef }
  let group : GoalGroup := {
    id := ← freshGroupId
    rootIndex
    members
    preGroup? := some preGroup
    prefixProofs
    prefixConsumed
    prefixMetaInfo
    externalPrefix?
    externalAncestors
    externalConsumed
    externalMetaInfo
    platform := Platform.empty members.size <|
      if obun.kind.isDuplicated then .shared else .disjoint
  }
  markResidualSpawned obun.id rootIndex trigger preGroup
  registerGroup obunRef group
  enqueueGroup group
  trace[iaesop.search.bubble] "iaesop(bubble): spawned residual group {group.id} for \
    obun {obun.id}; root={rootIndex}; members={indices}; prefix={preBubble}"
  return true

private def relevantToAnotherMember (group : GoalGroup) (sourceIndex : Nat)
    (bubble : ProofBubble) : BubbleM Q Bool := do
  for index in List.range group.members.size do
    if index != sourceIndex then
      let some member := group.members[index]?
        | throwError "iaesop(bubble): group member index is out of bounds"
      let sibling ← member.goal.get
      if bubble.metaInfo.any fun assignment =>
          sibling.unassignedMvars.contains assignment.mvarId then
        return true
  return false

private def spawnMetaResidualGroup (obunRef : ObunRef) (group : GoalGroup)
    (sourceIndex : Nat) (bubble : ProofBubble) : BubbleM Q Bool := do
  if bubble.metaInfo.isEmpty || !(← relevantToAnotherMember group sourceIndex bubble) then
    return false
  let some prefixConsumed := appendResources group.platform.resourcePolicy
      group.prefixConsumed bubble.consumed | return false
  let some parentRappRef := (← obunRef.get).parent? | return false
  let parentRapp ← parentRappRef.get
  let some prefixMetaInfo ← mergeMetaInfo parentRapp.metaState
      #[group.prefixMetaInfo, bubble.metaInfo] | return false
  let some source := group.members[sourceIndex]?
    | throwError "iaesop(bubble): source group member is out of bounds"
  let prefixProofs := group.prefixProofs.push (source.originalIndex, bubble.id)
  let indices := group.members.mapIdx (fun index member => (index, member))
    |>.filter (fun entry => entry.1 != sourceIndex)
    |>.map (fun entry => entry.2.originalIndex)
  mkResidualGroup obunRef group.rootIndex indices prefixProofs prefixConsumed prefixMetaInfo
    group.externalPrefix? group.externalAncestors group.externalConsumed
    group.externalMetaInfo bubble.id group.id bubble.id

private def saveCompletion (completion : GroupCompletion) : BubbleM Q Unit :=
  modifyThe State fun state => {
    state with groupCompletions := state.groupCompletions.push completion
  }

private def mkCompletion (obunRef : ObunRef) (group : GoalGroup)
    (combination : Combination IrisHyp) : BubbleM Q (Option GroupCompletion) := do
  let some consumed := appendResources group.platform.resourcePolicy
      group.prefixConsumed combination.consumed
    | return none
  let currentProofs ← combination.selected.mapM fun candidate => do
    let some member := group.members[candidate.childIndex]?
      | throwError "iaesop(bubble): group combination member is out of bounds"
    return (member.originalIndex, candidate.id)
  let proofs := group.prefixProofs ++ currentProofs
  let bubbles ← proofs.mapM fun (_, bubbleId) => getBubble bubbleId
  let some parentRappRef := (← obunRef.get).parent? | return none
  let parentRapp ← parentRappRef.get
  let some metaInfo ← mergeMetaInfo parentRapp.metaState <|
      #[group.externalMetaInfo] ++ bubbles.map (fun bubble => bubble.metaInfo)
    | return none
  let some representativeEntry := proofs.foldl (init := none) fun best proof =>
      match best with
      | none => some proof
      | some old => if old.1 < proof.1 then some proof else some old
    | return none
  let completion : GroupCompletion := {
    id := ← freshBubbleId
    obunId := (← obunRef.get).id
    groupId := group.id
    rootIndex := group.rootIndex
    proofs
    consumed
    metaInfo
    externalPrefix? := group.externalPrefix?
    externalAncestors := group.externalAncestors
    reservedConsumed := group.externalConsumed ++ consumed
    representative := representativeEntry.2
  }
  saveCompletion completion
  return some completion

private def orderedProofs (obun : Obun)
    (completions : Array GroupCompletion) : BubbleM Q (Array BubbleId) := do
  let proofs := completions.foldl (init := #[]) fun acc completion =>
    acc ++ completion.proofs
  (List.range obun.goals.size).toArray.mapM fun originalIndex =>
    match proofs.find? fun proof => proof.1 == originalIndex with
    | some (_, bubbleId) => pure bubbleId
    | none => throwError "iaesop(bubble): completed groups do not cover child {originalIndex}"

private def completionCoversRoot (completion : GroupCompletion)
    (rootIndex : Nat) : BubbleM Q Bool := do
  if completion.rootIndex == rootIndex then return true
  for ancestorId in completion.externalAncestors do
    if (← getGroupCompletion ancestorId).rootIndex == rootIndex then return true
  return false

private def spawnLinearResidualFrom (obunRef : ObunRef)
    (completion : GroupCompletion) (targetRoot : Nat) : BubbleM Q Unit := do
  if ← completionCoversRoot completion targetRoot then return
  let obun ← obunRef.get
  let some indices := obun.bubbleDependencyRoots[targetRoot]? | return
  let _ ← mkResidualGroup obunRef targetRoot indices #[] #[] #[]
    (some completion.id) (completion.externalAncestors.push completion.id)
    completion.reservedConsumed completion.metaInfo completion.id
    completion.groupId completion.representative
  return

private def hasLinearResidualFor (obunId : ObunId) (targetRoot : Nat) :
    BubbleM Q Bool :=
  return (← getThe State).spawnedGroups.any fun entry =>
    entry.obunId == obunId && entry.rootIndex == targetRoot

private def reservesFullManagedContext (obun : Obun)
    (completion : GroupCompletion) : Bool :=
  match obun.fullContextIrisSubgoals[0]? with
  | none => false
  | some template =>
      let incoming := (spatialHypEntries template.hyps).map fun (_, ivar, _) => ivar
      !incoming.isEmpty && incoming.all fun ivar =>
        completion.reservedConsumed.any fun used => used.ivar == ivar

/- Generate remaining-context work only after ordinary speculative search has
stalled.  "No bubble yet" while a sibling is still queued is not failure and
must not clone the sibling search. -/
def spawnBlockedLinearResidualGroups : BubbleM Q Bool := do
  for (_, obunRef) in (← getThe State).platformObuns do
    let obun ← obunRef.get
    let some platform := obun.bubblePlatform? | continue
    if obun.kind.isManaged && platform.emitted.isEmpty then
      for sourceRoot in List.range platform.byChild.size do
        for candidate in platform.byChild[sourceRoot]! do
          let completion ← getGroupCompletion candidate.id
          for targetRoot in List.range platform.byChild.size do
            if targetRoot != sourceRoot then
              let targets := platform.byChild[targetRoot]!
              if targets.isEmpty then
                let before := (← obunRef.get).bubbleGroups.size
                spawnLinearResidualFrom obunRef completion targetRoot
                if (← obunRef.get).bubbleGroups.size > before then return true
              else
                for target in targets do
                  if resourcesConflict candidate.consumed target.consumed then
                    let other ← getGroupCompletion target.id
                    let before := (← obunRef.get).bubbleGroups.size
                    spawnLinearResidualFrom obunRef completion targetRoot
                    if (← obunRef.get).bubbleGroups.size > before then return true
                    let before := (← obunRef.get).bubbleGroups.size
                    spawnLinearResidualFrom obunRef other sourceRoot
                    if (← obunRef.get).bubbleGroups.size > before then return true
  return false

structure GroupEmission where
  rapp : RappRef
  children : Array BubbleId
  consumed : Array IrisHyp

private def arriveCompletion (obunRef : ObunRef) (completion : GroupCompletion) :
    BubbleM Q (Array GroupEmission) := do
  let obun ← obunRef.get
  let some currentPlatform := obun.bubblePlatform?
    | throwError "iaesop(bubble): Obun {obun.id} has no Bubble platform"
  let candidate : Candidate IrisHyp := {
    id := completion.id
    childIndex := completion.rootIndex
    consumed := completion.consumed
    pre := completion.externalPrefix?
    constituents := completion.externalAncestors
  }
  let (platform, combinations) := arrive currentPlatform candidate
  obunRef.modify fun current => current.setBubblePlatform? (some platform)
  /- A managed sibling can require the context left by this completion before
  it can emit any full-context bubble at all (recursive BI rules are a common
  example).  Start one such reservation eagerly, but never clone it for every
  alternative bubble.  If it exhausts, the stalled-platform fallback below
  can advance to the next source candidate. -/
  if obun.kind.isManaged && combinations.isEmpty &&
      reservesFullManagedContext obun completion then
    for targetRoot in List.range platform.byChild.size do
      if targetRoot != completion.rootIndex && platform.byChild[targetRoot]!.isEmpty &&
          !(← hasLinearResidualFor obun.id targetRoot) then
        spawnLinearResidualFrom obunRef completion targetRoot
  let some rapp := obun.parent? | return #[]
  combinations.mapM fun combination => do
    let completions ← combination.selected.mapM fun candidate =>
      getGroupCompletion candidate.id
    return {
      rapp
      children := ← orderedProofs obun completions
      consumed := combination.consumed
    }

def arriveGoalBubble (bubble : ProofBubble) : BubbleM Q (Array GroupEmission) := do
  let goal ← bubble.goal.get
  let obunRef := goal.parent
  let locations ← findGroupLocations (← obunRef.get) goal.id
  let mut emissions := #[]
  for location in locations do
    let group ← getGroup obunRef location.groupId
    /- A bubble that fixes a metavariable used by another member is a prefix,
    not an ordinary alternative in the old group.  Only its residual group
    may combine subsequent sibling bubbles with that assignment. -/
    if ← spawnMetaResidualGroup obunRef group location.memberIndex bubble then
      continue
    let candidate : Candidate IrisHyp := {
      id := bubble.id
      childIndex := location.memberIndex
      consumed := bubble.consumed
    }
    let (platform, combinations) := arrive group.platform candidate
    setGroup obunRef { group with platform }
    for combination in combinations do
      let some completion ← mkCompletion obunRef group combination | continue
      trace[iaesop.search.bubble] "iaesop(bubble): group {group.id} completed as \
        {completion.id}; root={group.rootIndex}; proofs={completion.proofs.size}"
      emissions := emissions ++ (← arriveCompletion obunRef completion)
  return emissions

end Iris.ProofMode.Aesop.Search.Bubble
