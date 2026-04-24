module

public meta import Aesop
public meta import Iris.ProofMode.Tactics.Aesop.Frontend

public section

open Lean
open Lean.Elab.Tactic

namespace Iris.ProofMode.Tactics.Aesop

@[tactic Parser.iaesopTactic, tactic Parser.iaesopTactic?]
meta def evalIaesop : Tactic := fun _ => do
  throwError "iaesop is not implemented yet"

end Iris.ProofMode.Tactics.Aesop
