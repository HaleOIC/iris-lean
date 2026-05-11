module

public meta import Batteries.Lean.Meta.SavedState
public meta import Lean.Meta.Tactic.Simp.SimpAll
public meta import Iris.ProofMode.Aesop.Search.Types
public meta import Iris.ProofMode.Aesop.Search.SearchM

public meta section

namespace Iris.ProofMode.Aesop

open Lean Lean.Meta

-- namespace NormM

-- structure Context where
--   maxIterations : Nat
--   enableSimp : Bool
--   goalMVars : Std.HashSet MVarId

-- end NormM

-- abbrev NormM := ReaderT NormM.Context MetaM

-- instance : MonadBacktrack SavedState NormM where
--   saveState := Meta.saveState
--   restoreState s := s.restore

-- inductive NormSeqResult where
--   | proved
--   | changed (goal : MVarId)
--   | unchanged

-- abbrev NormStep := MVarId → NormM NormSeqResult

-- private inductive SimpNormResult where
--   | solved
--   | unchanged
--   | simplified (newGoal : MVarId)

-- private def simpGoalWithAllHypotheses (goal : MVarId) :
--     MetaM SimpNormResult := do
--   goal.withContext do
--     let ctx ← Simp.mkContext
--       (config := ({} : Simp.Config))
--       (simpTheorems := #[← getSimpTheorems])
--       (congrTheorems := ← getSimpCongrTheorems)
--     let ctx := ctx.setFailIfUnchanged false
--     let lctx ← getLCtx
--     let mut fvarIdsToSimp := Array.mkEmpty lctx.decls.size
--     for ldecl in lctx do
--       if ldecl.isImplementationDetail then
--         continue
--       fvarIdsToSimp := fvarIdsToSimp.push ldecl.fvarId
--     let (result?, _) ←
--       Meta.simpGoal goal ctx (simprocs := #[]) (discharge? := none)
--         (simplifyTarget := true) (fvarIdsToSimp := fvarIdsToSimp)
--     match result? with
--     | none =>
--       return .solved
--     | some (_, newGoal) =>
--       if newGoal == goal then
--         return .unchanged
--       else
--         return .simplified newGoal

-- private def anyGoalMVarDropped : NormM Bool := do
--   let mvars := (← read).goalMVars
--   for mvar in mvars do
--     if !(← mvar.isAssignedOrDelayedAssigned) then
--       return true
--   return false

-- namespace NormStep

-- def simp : NormStep := fun goal => do
--   if !(← read).enableSimp then
--     return .unchanged
--   let preState ← saveState
--   match ← simpGoalWithAllHypotheses goal with
--   | .solved =>
--     if ← anyGoalMVarDropped then
--       restoreState preState
--       return .unchanged
--     else
--       return .proved
--   | .unchanged =>
--     return .unchanged
--   | .simplified newGoal =>
--     return .changed newGoal

-- end NormStep

-- private partial def runNormSteps (goal : MVarId)
--     (steps : Array NormStep) : NormM NormSeqResult := do
--   if steps.isEmpty then
--     return .unchanged
--   go 0 goal false
-- where
--   go (iteration : Nat) (goal : MVarId) (anySuccess : Bool) :
--       NormM NormSeqResult := do
--     let maxIterations := (← read).maxIterations
--     if iteration < maxIterations then
--       match ← runFrom 0 goal with
--       | .proved =>
--         return .proved
--       | .changed newGoal =>
--         go (iteration + 1) newGoal true
--       | .unchanged =>
--         if anySuccess then
--           return .changed goal
--         else
--           return .unchanged
--     else
--       throwError
--         "iaesop: exceeded maximum number of normalisation iterations ({maxIterations}). This means normalisation probably got stuck in an infinite loop."
--   runFrom (i : Nat) (goal : MVarId) : NormM NormSeqResult := do
--     if h : i < steps.size then
--       match ← steps[i] goal with
--       | .unchanged => runFrom (i + 1) goal
--       | result => return result
--     else
--       return .unchanged

-- private def normalizeGoalMVar (goal : MVarId) : NormM NormSeqResult := do
--   let normSteps := #[NormStep.simp]
--   runNormSteps goal normSteps

variable {Q : Type} [Queue Q]

def normalizeGoal (gref : GoalRef) : SearchM Q Unit := do
  let g ← gref.get
  let preGoal := g.preNormGoal
  match g.normalizationState with
  | .provenByNorm .. =>
    gref.modify λ g => g.setState .provenByNormalization
  | .normal .. =>
    return
  | .notNormal =>
    gref.modify λ g =>
      g.setNormalizationState (.normal preGoal g.preNormState #[])


end Aesop
