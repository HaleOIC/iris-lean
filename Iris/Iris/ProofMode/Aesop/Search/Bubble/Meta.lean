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

/- A branch-local expression metavariable declaration may mention fresh
universe metavariables.  Copy those declarations and assignments before the
expression declaration; otherwise restoring the platform state leaves a
well-named expression metavariable whose type contains unknown universes. -/
private def copyUniverseContext (source : SavedState) : MetaM Unit := do
  let sourceMCtx := source.meta.mctx
  modifyMCtx fun current =>
    let lDecls := sourceMCtx.lDecls.foldl (init := current.lDecls) fun decls id decl =>
      if decls.contains id then decls else decls.insert id decl
    let lAssignment := sourceMCtx.lAssignment.foldl
        (init := current.lAssignment) fun assignments id value =>
      if assignments.contains id then assignments else assignments.insert id value
    { current with
      lmvarCounter := max current.lmvarCounter sourceMCtx.lmvarCounter
      lDecls
      lAssignment }

/- Local contexts are persistent snapshots.  A declaration copied from one
branch can refer to another branch-local declaration that is not reachable
from its target expression alone (for example through a local declaration's
value).  Transfer the branch's declaration table, but deliberately not its
expression assignments: assignments are merged separately and checked for
compatibility. -/
private def copyBranchDeclarations (source : SavedState) : MetaM Unit := do
  copyUniverseContext source
  let sourceMCtx := source.meta.mctx
  modifyMCtx fun current =>
    let decls := sourceMCtx.decls.foldl (init := current.decls) fun decls id decl =>
      if decls.contains id then decls else decls.insert id decl
    { current with
      mvarCounter := max current.mvarCounter sourceMCtx.mvarCounter
      decls }

private partial def copyExprMVarDecl (source : SavedState) (mvarId : MVarId)
    (visited : Std.HashSet MVarId := {}) : MetaM Unit := do
  if visited.contains mvarId then return
  let visited := visited.insert mvarId
  let (decl, dependencies) ← source.runMetaM' do
    let decl ← mvarId.getDecl
    let dependencies ← mvarId.getMVarDependencies (includeDelayed := true)
    return (decl, dependencies)
  copyUniverseContext source
  unless ← mvarId.isDeclared do
    modifyMCtx fun mctx => {
      mctx with
      mvarCounter := max mctx.mvarCounter source.meta.mctx.mvarCounter
      decls := mctx.decls.insert mvarId decl
    }
  /- Even when the declaration itself already exists in the platform state,
  the source branch can contain additional declarations referenced from its
  local context.  Do not return early before transferring those dependencies. -/
  for dependency in dependencies do
    copyExprMVarDecl source dependency visited

private def prepareAssignment (assignment : MetaAssignment) : MetaM Unit := do
  copyBranchDeclarations assignment.sourceState
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
