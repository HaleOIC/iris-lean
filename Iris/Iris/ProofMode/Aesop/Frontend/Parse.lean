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

private meta def parsePureSolver (stx : Syntax) : TermElabM Syntax := do
  match stx with
  | `(iaesopPureSolver| pureBy $solver:tactic) => pure solver.raw
  | _ => throwUnsupportedSyntax

private meta def parseSuccessProbability (p : Syntax) : TermElabM Percent := do
  let some p := p.isNatLit?
    | throwError "iaesop: expected a numeral success probability for local rule"
  match Percent.ofNat p with
  | some p => return p
  | none => throwError
      "iaesop: local rule success probability '{p}%' is not between 0 and 100"

private meta def parseRuleDecl (declStx : Syntax) : TermElabM Name := do
  Lean.Elab.realizeGlobalConstNoOverloadWithInfo declStx

private meta def parseRuleDirection (stx : Syntax) : TermElabM RuleBuilderKind := do
  match stx with
  | `(iaesopRuleDirection| backward) => pure .backward
  | `(iaesopRuleDirection| forward) => pure .forward
  | _ => throwUnsupportedSyntax

private meta def parseLocalRule (stx : Syntax) : TermElabM LocalTheoremRule := do
  match stx with
  | `(iaesopLocalRule| $dir:iaesopRuleDirection $declStx:ident) =>
      return {
        kind := ← parseRuleDirection dir
        decl := ← parseRuleDecl declStx
      }
  | `(iaesopLocalRule| $dir:iaesopRuleDirection $declStx:ident $p:num %) =>
      return {
        kind := ← parseRuleDirection dir
        decl := ← parseRuleDecl declStx
        successProbability := ← parseSuccessProbability p
      }
  | _ => throwUnsupportedSyntax

private meta def parseErasedRule (stx : Syntax) : TermElabM ErasedTheoremRule := do
  match stx with
  | `(iaesopErasedRule| $dir:iaesopRuleDirection $declStx:ident) =>
      return {
        kind := ← parseRuleDirection dir
        decl := ← parseRuleDecl declStx
      }
  | _ => throwUnsupportedSyntax

private meta def parseRuleEdit (stx : Syntax) :
    TermElabM (Array LocalTheoremRule × Array ErasedTheoremRule) := do
  match stx with
  | `(iaesopRuleEdit| with [$[$rules:iaesopLocalRule],*]) =>
      return (← rules.mapM parseLocalRule, #[])
  | `(iaesopRuleEdit| without [$[$rules:iaesopErasedRule],*]) =>
      return (#[], ← rules.mapM parseErasedRule)
  | _ => throwUnsupportedSyntax

private meta def parseRuleEdits (edits : Array (TSyntax `iaesopRuleEdit)) :
    TermElabM (Array LocalTheoremRule × Array ErasedTheoremRule) := do
  let mut localTheoremRules := #[]
  let mut erasedTheoremRules := #[]
  for edit in edits do
    let (newRules, erasedRules) ← parseRuleEdit edit
    localTheoremRules := localTheoremRules ++ newRules
    erasedTheoremRules := erasedTheoremRules ++ erasedRules
  return (localTheoremRules, erasedTheoremRules)

private meta def mkConfig (trace : Bool) (strategyStx? : Option (TSyntax `iaesopStrategy))
    (normModeStx? : Option (TSyntax `iaesopNormMode))
    (ruleSetStx? : Option (TSyntax `iaesopRuleSet))
    (pureSolverStx? : Option (TSyntax `iaesopPureSolver))
    (ruleEdits : Array (TSyntax `iaesopRuleEdit)) : TermElabM SearchConfig := do
  let strategy ← match strategyStx? with
    | none => pure .bestFirst
    | some strategyStx => parseStrategy strategyStx
  let (enableSimp, enableUnfold) ← match normModeStx? with
    | none => pure (false, false)
    | some normModeStx => parseNormMode normModeStx
  let useBaseline ← match ruleSetStx? with
    | none => pure false
    | some ruleSetStx => parseRuleSet ruleSetStx
  let pureSolver ← match pureSolverStx? with
    | none => pure defaultPureSolver
    | some pureSolverStx => parsePureSolver pureSolverStx
  let (localTheoremRules, erasedTheoremRules) ← parseRuleEdits ruleEdits
  return {
    generateScript? := trace
    strategy := strategy
    enableSimp? := enableSimp
    enableUnfold? := enableUnfold
    baseline? := useBaseline
    pureSolver
    localTheoremRules
    erasedTheoremRules
  }

/- Parse given syntax into search configuration -/
meta def parse (stx : Syntax) : TermElabM SearchConfig := do
  withRef stx do
    match stx with
    | `(tactic| iaesop $[$strategy:iaesopStrategy]? $[$normMode:iaesopNormMode]?
        $[$ruleSet:iaesopRuleSet]? $[$pureSolver:iaesopPureSolver]?
        $[$ruleEdits:iaesopRuleEdit]*) =>
        mkConfig false strategy normMode ruleSet pureSolver ruleEdits
    | `(tactic| iaesop? $[$strategy:iaesopStrategy]? $[$normMode:iaesopNormMode]?
        $[$ruleSet:iaesopRuleSet]? $[$pureSolver:iaesopPureSolver]?
        $[$ruleEdits:iaesopRuleEdit]*) =>
        mkConfig true strategy normMode ruleSet pureSolver ruleEdits
    | _ =>
        throwUnsupportedSyntax

end Iris.ProofMode.Aesop
