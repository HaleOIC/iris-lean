module

public meta import Iris.ProofMode.Tactics.Basic
public meta import Iris.ProofMode.Aesop.Frontend.Basic
public meta import Iris.ProofMode.Aesop.Search.Shared.Configure

public meta section

namespace Iris.ProofMode.Aesop

open Lean Elab Tactic

private meta def parseAlgorithm (stx : Syntax) : TermElabM SearchAlgorithm := do
  match stx with
  | `(iaesopAlgorithm| baseline) => pure .copy
  | `(iaesopAlgorithm| copy) => pure .copy
  | `(iaesopAlgorithm| bubble) => pure .bubble
  | _ => throwUnsupportedSyntax

private meta def parseNormMode (stx : Syntax) : TermElabM (Bool × Bool) := do
  match stx with
  | `(iaesopNormMode| unfold) => pure (false, true)
  | `(iaesopNormMode| simp) => pure (true, false)
  | `(iaesopNormMode| normAll) => pure (true, true)
  | _ => throwUnsupportedSyntax

private meta def parseStrategy (stx : Syntax) : TermElabM Strategy := do
  match stx with
  | `(iaesopStrategy| bestFirst) => pure .bestFirst
  | `(iaesopStrategy| depthFirst) => pure .depthFirst
  | `(iaesopStrategy| breadthFirst) => pure .breadthFirst
  | _ => throwUnsupportedSyntax

private meta def parsePureSolver (stx : Syntax) : TermElabM (Bool × Syntax) := do
  match stx with
  | `(iaesopPureSolver| pureBy $solver:tactic) => pure (false, solver.raw)
  | `(iaesopPureSolver| pureStop) => pure (true, defaultPureSolver)
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

private meta def mkConfig (generateScript? : Bool)
    (algorithmStx? : Option (TSyntax `iaesopAlgorithm))
    (strategyStx? : Option (TSyntax `iaesopStrategy))
    (normModeStx? : Option (TSyntax `iaesopNormMode))
    (pureSolverStx? : Option (TSyntax `iaesopPureSolver))
    (ruleEdits : Array (TSyntax `iaesopRuleEdit)) : TermElabM SearchConfig := do
  let algorithm ← match algorithmStx? with
    | none => pure .copy
    | some algorithmStx => parseAlgorithm algorithmStx
  let strategy ← match strategyStx? with
    | none => pure .bestFirst
    | some strategyStx => parseStrategy strategyStx
  let (enableSimp?, enableUnfold?) ← match normModeStx? with
    | none => pure (false, false)
    | some normModeStx => parseNormMode normModeStx
  let (pureStop?, pureSolver) ← match pureSolverStx? with
    | none => pure (false, defaultPureSolver)
    | some pureSolverStx => parsePureSolver pureSolverStx
  let (localTheoremRules, erasedTheoremRules) ← parseRuleEdits ruleEdits
  return {
    algorithm
    generateScript?
    strategy
    enableSimp?
    enableUnfold?
    pureSolver
    pureStop?
    localTheoremRules
    erasedTheoremRules
  }

/- Parse given syntax into search configuration -/
meta def parse (stx : Syntax) : TermElabM SearchConfig := do
  withRef stx do
    match stx with
    | `(tactic| iaesop $[$algorithm:iaesopAlgorithm]?
        $[$strategy:iaesopStrategy]? $[$normMode:iaesopNormMode]?
        $[$pureSolver:iaesopPureSolver]?
        $[$ruleEdits:iaesopRuleEdit]*) =>
        mkConfig false algorithm strategy normMode pureSolver ruleEdits
    | `(tactic| iaesop? $[$algorithm:iaesopAlgorithm]?
        $[$strategy:iaesopStrategy]? $[$normMode:iaesopNormMode]?
        $[$pureSolver:iaesopPureSolver]?
        $[$ruleEdits:iaesopRuleEdit]*) =>
        mkConfig true algorithm strategy normMode pureSolver ruleEdits
    | _ =>
        throwUnsupportedSyntax

end Iris.ProofMode.Aesop
