module

public meta import Iris.ProofMode.Aesop.Tree.Impl
public meta import Iris.ProofMode.Aesop.Util.Basic

public meta section

open Lean Lean.Meta Std
open Iris.ProofMode.Aesop

namespace Iris.ProofMode.Aesop

namespace Obun

@[inline]
protected def mk : ObunData GoalRef RappRef → Obun :=
  tree.introObun

instance : Nonempty Obun :=
  ⟨Obun.mk {
    id := .zero
    parent? := none
    goals := #[]
    state := .unknown
    isIrrelevant := false
    kind := .plain
    scriptSteps? := none
    metaState? := none
  }⟩

@[inline]
protected def elim : Obun → ObunData GoalRef RappRef :=
  tree.elimObun

@[inline]
protected def modify
    (f : ObunData GoalRef RappRef → ObunData GoalRef RappRef)
    (o : Obun) : Obun :=
  Obun.mk $ f $ o.elim

@[inline]
def id (o : Obun) : ObunId :=
  o.elim.id

@[inline]
def parent? (o : Obun) : Option RappRef :=
  o.elim.parent?

@[inline]
def goals (o : Obun) : Array GoalRef :=
  o.elim.goals

@[inline]
def state (o : Obun) : NodeState :=
  o.elim.state

@[inline]
def isIrrelevant (o : Obun) : Bool :=
  o.elim.isIrrelevant

@[inline]
def kind (o : Obun) : ObunKind :=
  o.elim.kind

@[inline]
def scriptSteps? (o : Obun) : Option (Array Script.LazyStep) :=
  o.elim.scriptSteps?

@[inline]
def metaState? (o : Obun) : Option SavedState :=
  o.elim.metaState?

@[inline]
def setId (id : ObunId) (o : Obun) : Obun :=
  o.modify fun o => { o with id }

@[inline]
def setParent (parent : RappRef) (o : Obun) : Obun :=
  o.modify fun o => { o with parent? := some parent }

@[inline]
def setGoals (goals : Array GoalRef) (o : Obun) : Obun :=
  o.modify fun o => { o with goals }

@[inline]
def setState (state : NodeState) (o : Obun) : Obun :=
  o.modify fun o => { o with state }

@[inline]
def setIsIrrelevant (isIrrelevant : Bool) (o : Obun) : Obun :=
  o.modify fun o => { o with isIrrelevant }

@[inline]
def setKind (kind : ObunKind) (o : Obun) : Obun :=
  o.modify fun o => { o with kind }

@[inline]
def setScriptSteps? (scriptSteps? : Option (Array Script.LazyStep))
    (o : Obun) : Obun :=
  o.modify fun o => { o with scriptSteps? }

@[inline]
def setMetaState? (metaState? : Option SavedState) (o : Obun) : Obun :=
  o.modify fun o => { o with metaState? }

instance : BEq Obun where
  beq o₁ o₂ := o₁.id == o₂.id

instance : Hashable Obun where
  hash o := hash o.id

end Obun

namespace Goal

@[inline]
protected def mk : GoalData RappRef ObunRef → Goal :=
  tree.introGoal

instance : Nonempty Goal :=
  ⟨Goal.mk Classical.ofNonempty⟩

@[inline]
protected def elim : Goal → GoalData RappRef ObunRef :=
  tree.elimGoal

@[inline]
protected def modify
    (f : GoalData RappRef ObunRef → GoalData RappRef ObunRef)
    (g : Goal) : Goal :=
  Goal.mk $ f $ g.elim

@[inline]
def id (g : Goal) : GoalId :=
  g.elim.id

@[inline]
def mask (g : Goal) : ProgressMask :=
  g.elim.mask

@[inline]
def parent (g : Goal) : ObunRef :=
  g.elim.parent

@[inline]
def children (g : Goal) : Array RappRef :=
  g.elim.children

@[inline]
def origin (g : Goal) : GoalOrigin :=
  g.elim.origin

@[inline]
def depth (g : Goal) : Nat :=
  g.elim.depth

@[inline]
def state (g : Goal) : GoalState :=
  g.elim.state

@[inline]
def isIrrelevant (g : Goal) : Bool :=
  g.elim.isIrrelevant

@[inline]
def isForcedUnprovable (g : Goal) : Bool :=
  g.elim.isForcedUnprovable

@[inline]
def preNormGoal (g : Goal) : MVarId :=
  g.elim.preNormGoal

@[inline]
def preNormState (g : Goal) : SavedState :=
  g.elim.preNormState

@[inline]
def normalizationState (g : Goal) : NormalizationState :=
  g.elim.normalizationState

@[inline]
def unassignedMvars (g : Goal) : HashSet MVarId :=
  g.elim.unassignedMvars

@[inline]
def successProbability (g : Goal) : Percent :=
  g.elim.successProbability

@[inline]
def addedInIteration (g : Goal) : Iteration :=
  g.elim.addedInIteration

@[inline]
def lastExpandedInIteration (g : Goal) : Iteration :=
  g.elim.lastExpandedInIteration

@[inline]
def rulesQueue (g : Goal) : RuleQueue :=
  g.elim.rulesQueue

@[inline]
def appendiedGoalId (g : Goal) : Array GoalId :=
  g.elim.appendiedGoalId

@[inline]
def rappChildren? (g : Goal) : Option (Array RappRef) :=
  some g.children

@[inline]
def hasNoChildren (g : Goal) : Bool :=
  g.children.isEmpty

@[inline]
def setId (id : GoalId) (g : Goal) : Goal :=
  g.modify fun g => { g with id }

@[inline]
def setMask (mask : ProgressMask) (g : Goal) : Goal :=
  g.modify λ g => { g with mask }

@[inline]
def setParent (parent : ObunRef) (g : Goal) : Goal :=
  g.modify fun g => { g with parent }

@[inline]
def setChildren (children : Array RappRef) (g : Goal) : Goal :=
  g.modify λ g => { g with children }

@[inline]
def setOrigin (origin : GoalOrigin) (g : Goal) : Goal :=
  g.modify fun g => { g with origin }

@[inline]
def setDepth (depth : Nat) (g : Goal) : Goal :=
  g.modify fun g => { g with depth }

@[inline]
def setState (state : GoalState) (g : Goal) : Goal :=
  g.modify fun g => { g with state }

@[inline]
def setIsIrrelevant (isIrrelevant : Bool) (g : Goal) : Goal :=
  g.modify fun g => { g with isIrrelevant }

@[inline]
def setIsForcedUnprovable (isForcedUnprovable : Bool) (g : Goal) : Goal :=
  g.modify fun g => { g with isForcedUnprovable }

@[inline]
def setPreNormGoal (preNormGoal : MVarId) (g : Goal) : Goal :=
  g.modify fun g => { g with preNormGoal }

@[inline]
def setPreNormState (preNormState : SavedState) (g : Goal) : Goal :=
  g.modify fun g => { g with preNormState }

@[inline]
def setNormalizationState
    (normalizationState : NormalizationState) (g : Goal) : Goal :=
  g.modify fun g => { g with normalizationState }

@[inline]
def setUnassignedMvars (unassignedMvars : HashSet MVarId) (g : Goal) : Goal :=
  g.modify fun g => { g with unassignedMvars }

@[inline]
def setSuccessProbability (successProbability : Percent) (g : Goal) : Goal :=
  g.modify fun g => { g with successProbability }

@[inline]
def setAddedInIteration (addedInIteration : Iteration) (g : Goal) : Goal :=
  g.modify fun g => { g with addedInIteration }

@[inline]
def setLastExpandedInIteration
    (lastExpandedInIteration : Iteration) (g : Goal) : Goal :=
  g.modify fun g => { g with lastExpandedInIteration }

@[inline]
def setRulesQueue (rulesQueue : RuleQueue) (g : Goal) : Goal :=
  g.modify fun g => { g with rulesQueue }

@[inline]
def setAppendiedGoalId (appendiedGoalId : Array GoalId) (g : Goal) : Goal :=
  g.modify fun g => { g with appendiedGoalId }

@[inline]
def mvar (g : Goal) : MVarId :=
  g.preNormGoal

@[inline]
def setMVar (mvar : MVarId) (g : Goal) : Goal :=
  g.setPreNormGoal mvar

instance : BEq Goal where
  beq g₁ g₂ := g₁.id == g₂.id

instance : Hashable Goal where
  hash g := hash g.id

end Goal

-- Goal related query during search
namespace Goal

protected def isActive (g : Goal) : BaseIO Bool :=
  return !g.isIrrelevant && g.state.isUnknown &&
    (!g.normalizationState.isNormal || !g.rulesQueue.isEmpty)

protected def isNormalized (g : Goal) : BaseIO Bool :=
  return g.normalizationState.isNormal

end Goal

namespace Rapp

@[inline]
protected def mk : RappData GoalRef ObunRef → Rapp :=
  tree.introRapp

instance : Nonempty Rapp :=
  ⟨Rapp.mk Classical.ofNonempty⟩

@[inline]
protected def elim : Rapp → RappData GoalRef ObunRef :=
  tree.elimRapp

@[inline]
protected def modify
    (f : RappData GoalRef ObunRef → RappData GoalRef ObunRef)
    (r : Rapp) : Rapp :=
  Rapp.mk $ f $ r.elim

@[inline]
def id (r : Rapp) : RappId :=
  r.elim.id

@[inline]
def parent (r : Rapp) : GoalRef :=
  r.elim.parent

@[inline]
def children (r : Rapp) : ObunRef :=
  r.elim.children

@[inline]
def state (r : Rapp) : NodeState :=
  r.elim.state

@[inline]
def isIrrelevant (r : Rapp) : Bool :=
  r.elim.isIrrelevant

@[inline]
def appliedRule (r : Rapp) : RegularRule :=
  r.elim.appliedRule

@[inline]
def successProbability (r : Rapp) : Percent :=
  r.elim.successProbability

@[inline]
def scriptSteps? (r : Rapp) : Option (Array Script.LazyStep) :=
  r.elim.scriptSteps?

@[inline]
def fullContextIrisSubgoals (r : Rapp) : Array IrisGoal :=
  r.elim.fullContextIrisSubgoals

@[inline]
def consumedSpatialHyp? (r : Rapp) : Option IrisHyp :=
  r.elim.consumedSpatialHyp?

@[inline]
def consumedLeanHyp? (r : Rapp) : Option FVarId :=
  r.elim.consumedLeanHyp?

@[inline]
def finalizedSpatialSplits (r : Rapp) : Array (Array IrisHyp) :=
  r.elim.finalizedSpatialSplits

@[inline]
def metaState (r : Rapp) : SavedState :=
  r.elim.metaState

@[inline]
def introducedMVars (r : Rapp) : HashSet MVarId :=
  r.elim.introducedMVars

@[inline]
def assignedMVars (r : Rapp) : HashSet MVarId :=
  r.elim.assignedMVars

@[inline]
def setId (id : RappId) (r : Rapp) : Rapp :=
  r.modify fun r => { r with id }

@[inline]
def setParent (parent : GoalRef) (r : Rapp) : Rapp :=
  r.modify fun r => { r with parent }

@[inline]
def setChildren (children : ObunRef) (r : Rapp) : Rapp :=
  r.modify fun r => { r with children }

@[inline]
def setState (state : NodeState) (r : Rapp) : Rapp :=
  r.modify fun r => { r with state }

@[inline]
def setIsIrrelevant (isIrrelevant : Bool) (r : Rapp) : Rapp :=
  r.modify fun r => { r with isIrrelevant }

@[inline]
def setAppliedRule (appliedRule : RegularRule) (r : Rapp) : Rapp :=
  r.modify fun r => { r with appliedRule }

@[inline]
def setSuccessProbability (successProbability : Percent) (r : Rapp) : Rapp :=
  r.modify fun r => { r with successProbability }

@[inline]
def setScriptSteps? (scriptSteps? : Option (Array Script.LazyStep))
    (r : Rapp) : Rapp :=
  r.modify fun r => { r with scriptSteps? }

@[inline]
def setfullContextIrisSubgoals (fullContextIrisSubgoals : Array IrisGoal) (r : Rapp) : Rapp :=
  r.modify λ r => { r with fullContextIrisSubgoals}

@[inline]
def setFullContextIrisSubgoals
    (fullContextIrisSubgoals : Array IrisGoal) (r : Rapp) : Rapp :=
  r.modify fun r => { r with fullContextIrisSubgoals }

@[inline]
def setconsumedSpatialHyp? (consumedSpatialHyp? : Option IrisHyp) (r : Rapp) : Rapp :=
  r.modify fun r => { r with consumedSpatialHyp? }

@[inline]
def setConsumedSpatialHyp? (consumedSpatialHyp? : Option IrisHyp) (r : Rapp) : Rapp :=
  r.modify fun r => { r with consumedSpatialHyp? }

@[inline]
def setConsumedLeanHyp? (consumedLeanHyp? : Option FVarId) (r : Rapp) : Rapp :=
  r.modify fun r => { r with consumedLeanHyp? }

@[inline]
def setfinalizedSpatialSplits (finalizedSpatialSplits : Array (Array IrisHyp)) (r : Rapp) : Rapp :=
  r.modify fun r => { r with finalizedSpatialSplits }

@[inline]
def setFinalizedSpatialSplits
    (finalizedSpatialSplits : Array (Array IrisHyp)) (r : Rapp) : Rapp :=
  r.modify fun r => { r with finalizedSpatialSplits }

@[inline]
def setMetaState (metaState : SavedState) (r : Rapp) : Rapp :=
  r.modify fun r => { r with metaState }

@[inline]
def setIntroducedMVars
    (introducedMVars : HashSet MVarId) (r : Rapp) : Rapp :=
  r.modify fun r => { r with introducedMVars }

@[inline]
def setAssignedMVars
    (assignedMVars : HashSet MVarId) (r : Rapp) : Rapp :=
  r.modify fun r => { r with assignedMVars }

instance : BEq Rapp where
  beq r₁ r₂ := r₁.id == r₂.id

instance : Hashable Rapp where
  hash r := hash r.id

end Rapp

end Iris.ProofMode.Aesop
