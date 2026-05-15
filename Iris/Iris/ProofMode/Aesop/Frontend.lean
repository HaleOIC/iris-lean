module

public meta import Iris.ProofMode.Tactics.Basic

public section

namespace Iris.ProofMode.Aesop.Frontend.Parser

syntax (name := iaesopTactic)  "iaesop" : tactic
syntax (name := iaesopTactic?) "iaesop?" : tactic
syntax (name := iaesopTacticSimp)  "iaesop" "+simp" : tactic
syntax (name := iaesopTacticSimp?) "iaesop?" "+simp" : tactic

end Iris.ProofMode.Aesop.Frontend.Parser
