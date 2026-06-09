module

public meta import Lean.Parser.Tactic
public import Iris.ProofMode.Aesop.Util.Percent
public import Iris.ProofMode.Aesop.Rule.Types.Name

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

/- A theorem rule added for a single `iaesop` invocation. -/
structure LocalTheoremRule where
  kind : RuleBuilderKind
  decl : Name
  successProbability : Percent := Percent.hundred
  deriving Inhabited

/- A theorem rule erased for a single `iaesop` invocation. -/
structure ErasedTheoremRule where
  kind : RuleBuilderKind
  decl : Name
  deriving Inhabited

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
  /- Extra theorem rules added only for this `iaesop` invocation. -/
  localTheoremRules : Array LocalTheoremRule := #[]
  /- Rule declarations removed only for this `iaesop` invocation. -/
  erasedTheoremRules : Array ErasedTheoremRule := #[]
