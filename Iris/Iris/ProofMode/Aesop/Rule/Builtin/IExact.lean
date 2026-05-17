module

public meta import Iris.ProofMode.Aesop.Rule.Common
public meta import Iris.ProofMode.Tactics.Assumption

public meta section

namespace Iris.ProofMode.Aesop.Rule.Builtin.IExact

open Lean Meta Qq Std
open Iris.BI
open Iris.ProofMode
open Iris.ProofMode.Aesop

variable {Q : Type} [Queue Q]

private structure IExactResult where
  used : Array UsedIrisHyp
  postState : SavedState

def run (parentRef : GoalRef) (_matchResult : RuleMatch) :
    SearchM Q (Array RappSpec) := do
  let parent ← parentRef.get
  let some goal := parent.normalizationState.normalizedGoal?
    | return #[]
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
    | return #[]
  if let some obunRef := managedObun? then
    obunRef.modify λ o => o.setMetaState? (some result.postState)
  return #[{
    rappState := .proven
    obunState := .proven
    obunKind := .plain
    childGoals := #[]
    fullContextIrisSubgoals := #[]
    consumedSpatialHyp? := none
    finalizedSpatialSplits := #[]
    metaState := result.postState
    parentState? := some (.provenByRuleApplication result.used)
  }]

end Iris.ProofMode.Aesop.Rule.Builtin.IExact
