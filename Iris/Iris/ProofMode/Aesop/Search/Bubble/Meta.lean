module

public meta import Batteries.Lean.Meta.SavedState
public meta import Iris.ProofMode.Aesop.Search.Bubble.BubbleM

public meta section

namespace Iris.ProofMode.Aesop.Search.Bubble

open Lean Meta Std
open Iris.ProofMode.Aesop

variable {Q : Type} [Queue Q]

def collectMetaInfo (state : SavedState) (mvars : Std.HashSet MVarId) :
    BubbleM Q (Array MetaAssignment) := do
  liftM (m := Iris.ProofMode.Aesop.CoreM Q) <| liftM (m := MetaM) <|
    state.runMetaM' do
      mvars.toArray.foldlM (init := #[]) fun assignments mvarId => do
        let some value ← getExprMVarAssignment? mvarId | return assignments
        let value ← instantiateMVars value
        return assignments.push { mvarId, value, sourceState := state }

def collectIncomingMetaInfo (goal : Goal) (state : SavedState) :
    BubbleM Q (Array MetaAssignment) := do
  let incomingMVars ← liftM (m := Iris.ProofMode.Aesop.CoreM Q) <|
    liftM (m := MetaM) <| goal.preNormState.runMetaM' do
      goal.preNormGoal.getMVarDependencies
  collectMetaInfo state incomingMVars

private partial def copyExprMVarDecl (source : SavedState) (mvarId : MVarId) :
    MetaM Unit := do
  if ← mvarId.isDeclared then return
  let (decl, dependencies) ← source.runMetaM' do
    let decl ← mvarId.getDecl
    let dependencies ← mvarId.getMVarDependencies (includeDelayed := true)
    return (decl, dependencies)
  modifyMCtx fun mctx => { mctx with decls := mctx.decls.insert mvarId decl }
  for dependency in dependencies do
    copyExprMVarDecl source dependency

private def prepareAssignment (assignment : MetaAssignment) : MetaM Unit := do
  for mvarId in ← getMVars assignment.value do
    copyExprMVarDecl assignment.sourceState mvarId

private def assignmentsCompatible (baseState : SavedState)
    (left right : MetaAssignment) : MetaM Bool :=
  baseState.runMetaM' do
    try
      prepareAssignment left
      prepareAssignment right
      isDefEq left.value right.value
    catch _ =>
      return false

/- Merge assignment deltas using Lean's definitional equality.  The check runs
in a disposable restoration of the platform's base state, augmented only with
declarations referenced by branch-local assignment values. -/
def mergeMetaInfo (baseState : SavedState)
    (parts : Array (Array MetaAssignment)) : BubbleM Q (Option (Array MetaAssignment)) := do
  let mut merged : Array MetaAssignment := #[]
  for part in parts do
    for assignment in part do
      match merged.find? fun old => old.mvarId == assignment.mvarId with
      | none => merged := merged.push assignment
      | some old =>
          let compatible ← liftM (m := Iris.ProofMode.Aesop.CoreM Q) <|
            liftM (m := MetaM) <| assignmentsCompatible baseState old assignment
          if !compatible then return none
  return some merged

/- Replay a bubble's assignment delta into a disposable copy of `baseState`.
The returned state can be used to instantiate a residual sibling goal. -/
def applyMetaInfo (baseState : SavedState) (metaInfo : Array MetaAssignment) :
    BubbleM Q (Option SavedState) := do
  liftM (m := Iris.ProofMode.Aesop.CoreM Q) <| liftM (m := MetaM) <|
    baseState.runMetaM' do
      try
        for assignment in metaInfo do
          copyExprMVarDecl assignment.sourceState assignment.mvarId
          prepareAssignment assignment
          if ← assignment.mvarId.isAssignedOrDelayedAssigned then
            unless ← isDefEq (mkMVar assignment.mvarId) assignment.value do
              return none
          else
            assignment.mvarId.assign assignment.value
        return some (← saveState)
      catch _ =>
        return none

end Iris.ProofMode.Aesop.Search.Bubble
