module

public meta import Iris.ProofMode.Tactics.Basic
public meta import Iris.ProofMode.Aesop.Frontend.Basic
public meta import Iris.ProofMode.Aesop.Search.Configure

public meta section

namespace Iris.ProofMode.Aesop

open Lean Elab Tactic

private meta def parseNormMode (stx : Syntax) : TermElabM (Bool × Bool) := do
  match stx with
  | `(iaesopNormMode| unfold) => pure (false, true)
  | `(iaesopNormMode| simp) => pure (true, false)
  | `(iaesopNormMode| normAll) => pure (true, true)
  | _ => throwUnsupportedSyntax

private meta def parseRuleSet (stx : Syntax) : TermElabM Bool := do
  match stx with
  | `(iaesopRuleSet| builtin) => pure false
  | `(iaesopRuleSet| baseline) => pure true
  | _ => throwUnsupportedSyntax

private meta def parseStrategy (stx : Syntax) : TermElabM Strategy := do
  match stx with
  | `(iaesopStrategy| bestFirst) => pure .bestFirst
  | `(iaesopStrategy| depthFirst) => pure .depthFirst
  | `(iaesopStrategy| breadthFirst) => pure .breadthFirst
  | _ => throwUnsupportedSyntax

private meta def mkConfig (trace : Bool) (strategyStx? : Option (TSyntax `iaesopStrategy))
    (normModeStx? : Option (TSyntax `iaesopNormMode))
    (ruleSetStx? : Option (TSyntax `iaesopRuleSet)) : TermElabM SearchConfig := do
  let strategy ← match strategyStx? with
    | none => pure .bestFirst
    | some strategyStx => parseStrategy strategyStx
  let (enableSimp, enableUnfold) ← match normModeStx? with
    | none => pure (false, false)
    | some normModeStx => parseNormMode normModeStx
  let useBaseline ← match ruleSetStx? with
    | none => pure false
    | some ruleSetStx => parseRuleSet ruleSetStx
  return {
    generateScript? := trace
    strategy := strategy
    enableSimp? := enableSimp
    enableUnfold? := enableUnfold
    baseline? := useBaseline
  }

/- Parse given syntax into search configuration -/
meta def parse (stx : Syntax) : TermElabM SearchConfig := do
  withRef stx do
    match stx with
    | `(tactic| iaesop $[$strategy:iaesopStrategy]? $[$normMode:iaesopNormMode]?
        $[$ruleSet:iaesopRuleSet]?) =>
        mkConfig false strategy normMode ruleSet
    | `(tactic| iaesop? $[$strategy:iaesopStrategy]? $[$normMode:iaesopNormMode]?
        $[$ruleSet:iaesopRuleSet]?) =>
        mkConfig true strategy normMode ruleSet
    | _ =>
        throwUnsupportedSyntax

end Iris.ProofMode.Aesop
