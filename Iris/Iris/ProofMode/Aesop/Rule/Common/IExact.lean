module

public meta import Iris.ProofMode.Aesop.Rule.Commit.Basic

public meta section

namespace Iris.ProofMode.Aesop.Rule.IExact

open Lean Meta Qq Std
open Iris.BI
open Iris.ProofMode

variable {Q : Type} [Queue Q]

def run (input : RuleInput) : SearchM Q RuleOutput := do
  let goal := input.goal
  let result? : Option (Option IrisHyp × SavedState) ← liftM do
    restoreState input.state
    goal.withContext do
      let goalType ← instantiateMVars (← goal.getType)
      let some { hyps, goal := target, .. } := parseIrisGoal? goalType
        | throwError "iaesop: internal error: iexact must work in iris proof-mode context"
      let some ⟨(inst, used), _, _, _, ty, b, _, _⟩ ←
          hyps.removeG false λ name ivar b ty => do
            let .some (inst, _) ← ProofMode.trySynthInstanceQ q(FromAssumption $b .in $ty $target)
              | return none
            let used : Option IrisHyp :=
              if isTrue b then none else some { name, ivar }
            return some (inst, used)
        | return none
      let _ : Q(FromAssumption $b .in $ty $target) := inst
      return some (used, ← saveState)
  let some result := result?
    | return {}
  match result.1 with
  | some hyp =>
    dbg_trace s!"iexact closed goal using spatial hypothesis {hyp.name}"
  | none =>
    dbg_trace "iexact closed goal using intuitionistic/persistent hypothesis"
  return RuleOutput.ofEffect result.2 (.closeGoal result.1)

end Iris.ProofMode.Aesop.Rule.IExact
