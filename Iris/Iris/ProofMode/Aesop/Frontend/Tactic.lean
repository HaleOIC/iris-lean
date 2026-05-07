module

public meta import Iris.ProofMode.Aesop.Frontend

public meta section

namespace Iris.ProofMode.Aesop.Frontend

open Lean Elab Tactic

-- TODO: add more options after first version
structure TacticConfig where
  -- Maximum number of rule applications in any branch of the search tree
  maxRuleApplicationDepth := 30
  -- Maximum number of norm rules applied to a single goal
  maxNormIterations := 100
  -- Enable iaesop prints a tactic proof after proving a goal
  traceScript : Bool := false
  -- Enable the builtin `simp` normalisation rule
  enableSimp : Bool := false
  deriving Inhabited, BEq, Repr

namespace TacticConfig

meta def parse (stx : Syntax) : TermElabM TacticConfig := do
  withRef stx do
    match stx with
    | `(tactic| iaesop) =>
        return { traceScript := false }
    | `(tactic| iaesop?) =>
        return { traceScript := true }
    | _ =>
        throwUnsupportedSyntax

end TacticConfig

end Iris.ProofMode.Aesop.Frontend
