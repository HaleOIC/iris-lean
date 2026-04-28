module

public import Aesop.Frontend
public import Iris.ProofMode.Aesop.Attr
public import Iris.ProofMode.Tactics.Assumption

namespace Iris.ProofMode.Aesop.Assumption

open Lean Aesop.RuleTac

@[aesop (rule_sets := [iris]) safe 0 tactic]
meta def iaesopAssumption : Aesop.RuleTac :=
  ofTacticSyntax λ _ => return Unhygienic.run `(tactic| iassumption)

end Assumption
