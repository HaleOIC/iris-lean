module

public meta import Iris.ProofMode.Aesop.Frontend.Main
public meta import Iris.ProofMode.Aesop.Search.Main

public section
namespace Iris.ProofMode.Aesop

open Lean Lean.Elab.Tactic
open Iris.ProofMode.Aesop.Search

private meta def evalIAesopCore (stx : Syntax) : TacticM Unit := do
  withRef stx do
  let config ← parse stx
  -- TODO: add [getRuleSet] here
  ProofModeM.runTactic λ mvar irisGoal => do
    let goals ← search mvar irisGoal config
    goals.forM Iris.ProofMode.addMVarGoal

@[tactic iaesopTactic, tactic iaesopTactic?]
meta def evalIAesop : Tactic := λ stx =>
  evalIAesopCore stx

end Iris.ProofMode.Aesop
