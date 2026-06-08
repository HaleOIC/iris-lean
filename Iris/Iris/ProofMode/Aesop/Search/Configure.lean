module

public meta import Lean.Parser.Tactic

public section

namespace Iris.ProofMode.Aesop

open Lean Meta

/- Search strategy iaesop can support -/
inductive Strategy
  | bestFirst
  | depthFirst
  | breadthFirst
  deriving Inhabited, BEq, Repr

/-- Default solver used for pure Lean goals produced by `ipureintro`. -/
def defaultPureSolver : Syntax :=
  .node .none ``_root_.Lean.Parser.Tactic.assumption #[.atom .none "assumption"]

structure SearchConfig where
  /- maximum depth of the search tree -/
  maxDepth : Nat := 100
  /- maximum rapp children for each goal -/
  maxRappNumber: Nat := 30
  /- maximum normalization iteration for each goal -/
  maxNormIterations: Nat := 20
  /- search strategy used during search (default: bestFirst) -/
  strategy : Strategy := Strategy.bestFirst
  /- whether generated script after proven (default: false) -/
  generateScript? : Bool := false
  /- whether enable simplifier during normalization stage (default: false) -/
  enableSimp? : Bool := false
  /- whether enable unfold during normalization stage (default: false) -/
  enableUnfold? : Bool := false
  /- whether select the baseline version (default: false) -/
  baseline? : Bool := false
  /- Solver run on pure Lean goals produced by `ipureintro`. -/
  pureSolver : Syntax := defaultPureSolver
