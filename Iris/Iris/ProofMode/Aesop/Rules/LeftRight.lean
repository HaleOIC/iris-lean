module

public import Aesop.Frontend
public import Iris.ProofMode.Aesop.Attr
public import Iris.ProofMode.Tactics.LeftRight

namespace Iris.ProofMode.Aesop.LeftRight

open Lean Aesop.RuleTac

@[aesop unsafe 50% tactic (rule_sets := [iris])]
meta def iaesopLeft : Aesop.RuleTac :=
  ofTacticSyntax λ _ => return Unhygienic.run `(tactic| ileft)

@[aesop unsafe 50% tactic (rule_sets := [iris])]
meta def iaesopRight : Aesop.RuleTac :=
  ofTacticSyntax λ _ => return Unhygienic.run `(tactic| iright)

end Iris.ProofMode.Aesop.LeftRight
