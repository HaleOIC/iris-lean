module

public meta import Aesop
public meta import Iris.ProofMode.Aesop.Frontend
public meta import Iris.ProofMode.Aesop.Rules

public section

open Lean
open Lean.Elab.Tactic

namespace Iris.ProofMode.Aesop

@[tactic Frontend.Parser.iaesopTactic, tactic Frontend.Parser.iaesopTactic?]
meta def evalIAesop : Tactic := λ stx => do
  -- TODO: add profileitM to measure the performance of `iaesop`
  match stx with
  | `(tactic| iaesop?) =>
    evalTactic (← `(tactic| aesop? (rule_sets := [-builtin, iris])))
  | `(tactic| iaesop) =>
    evalTactic (← `(tactic| aesop (rule_sets := [-builtin, iris])))
  | _ => throwError "unsupported iaesop syntax"

end Iris.ProofMode.Aesop
