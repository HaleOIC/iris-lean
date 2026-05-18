module

public import Iris.ProofMode.Aesop.Rule.Types.Name
public import Iris.ProofMode.Aesop.Util.Basic

public section

open Lean

namespace Iris.ProofMode.Aesop

inductive RuleBuilder where
  | identity
  | applyHyps
  | ipureIntro
  | imodintro
  | imod
  | tactic
  | iapply
  | iintro
  | iexact
  | iassumption
  | icases
  | ileft
  | iright
  | custom
  deriving Inhabited, BEq, Hashable, Ord

namespace RuleBuilder

instance : ToString RuleBuilder where
  toString
    | identity => "identity"
    | applyHyps => "applyHyps"
    | ipureIntro => "ipure_intro"
    | imodintro => "imodintro"
    | imod => "imod"
    | tactic => "tactic"
    | iapply => "iapply"
    | iintro => "iintro"
    | iexact => "iexact"
    | iassumption => "iassumption"
    | icases => "icases"
    | ileft => "ileft"
    | iright => "iright"
    | custom => "custom"

end RuleBuilder

structure RuleInfo where
  builder : RuleBuilder
  successProbability : Percent
  deriving Inhabited, BEq, Ord

namespace RuleInfo

instance : Hashable RuleInfo where
  hash rule := hash rule.builder

instance : ToFormat RuleInfo where
  format rule := Std.Format.text (toString rule.builder)

def ofBuilder (builder : RuleBuilder)
    (successProbability : Percent := Percent.hundred) : RuleInfo where
  builder
  successProbability

end RuleInfo

end Iris.ProofMode.Aesop
