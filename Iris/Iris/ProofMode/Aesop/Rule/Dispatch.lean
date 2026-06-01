module

public meta import Iris.ProofMode.Aesop.Rule.Common.Main
public meta import Iris.ProofMode.Aesop.Rule.Backward.Apply

public meta section

namespace Iris.ProofMode.Aesop

namespace RuleBuilder

def run {Q : Type} [Queue Q] : RuleBuilder → RuleRunner Q
  | .tactic descr => descr.run
  | .backward => Rule.Backward.run
  | _ => λ _ => return {}

def replay : RuleBuilder → RuleReplayer
  | .tactic descr => descr.replay
  | .backward => Rule.Backward.replay
  | _ => λ input => return #[input.goal]

end RuleBuilder

end Iris.ProofMode.Aesop
