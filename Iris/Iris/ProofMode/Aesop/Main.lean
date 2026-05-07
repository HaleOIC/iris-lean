module

public meta import Iris.ProofMode.Aesop.Frontend.Tactic
public meta import Iris.ProofMode.Aesop.Search

public section

open Lean
open Lean.Elab.Tactic

namespace Iris.ProofMode.Aesop

private meta def evalIAesopCore (stx : Syntax) : TacticM Unit := do
  withRef stx do
  let config ← Frontend.TacticConfig.parse stx
  -- TODO: add [getRuleSet] here
  ProofModeM.runTactic λ mvar irisGoal => do
    let goals ← search mvar irisGoal { traceScript := config.traceScript }
    goals.forM Iris.ProofMode.addMVarGoal

@[tactic Frontend.Parser.iaesopTactic, tactic Frontend.Parser.iaesopTactic?]
meta def evalIAesop : Tactic := λ stx =>
  evalIAesopCore stx

end Iris.ProofMode.Aesop
