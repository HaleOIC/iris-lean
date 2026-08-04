module

public meta import Iris.ProofMode.Aesop.Frontend.Main
public meta import Iris.ProofMode.Aesop.Search.Copy
public meta import Iris.ProofMode.Aesop.Search.Bubble

public section
namespace Iris.ProofMode.Aesop

open Lean Elab Tactic
open Iris.ProofMode.Aesop.Search

private meta def evalIAesopCore (stx : Syntax) : TacticM Unit := do
  withRef stx do
  let config ← parse stx
  -- TODO: add [getRuleSet] here
  let (subgoal, _) ← Iris.ProofMode.startProofMode (← getMainGoal)
  subgoal.withContext do
    let searchAction := match config.algorithm with
      | .copy => Search.Copy.search subgoal config
      | .bubble => Search.Bubble.search subgoal config
    let (remaining, _) ← StateRefT'.run searchAction {}
    -- make sure to synthesize everything postponed
    Term.synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := true)
    -- put the goals that depend on other goals last
    let dependees ← remaining.foldlM (λ m g => do return m ∪ (← g.getMVarDependencies)) ∅
    let (dep, nonDep) := remaining.partition dependees.contains
    replaceMainGoal (nonDep ++ dep).toList

@[tactic iaesopTactic, tactic iaesopTactic?]
meta def evalIAesop : Tactic := λ stx =>
  evalIAesopCore stx

end Iris.ProofMode.Aesop
