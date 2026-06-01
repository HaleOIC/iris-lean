module

public import Iris.ProofMode.Aesop.Rule.Types.Name
public import Iris.ProofMode.Aesop.Util.Basic

public section

open Lean

namespace Iris.ProofMode.Aesop

/- Tactic descriptor -/
inductive TacticDescr where
  | identity
  | icases
  | ipureIntro
  | ileft
  | iright
  | iexist
  | imodIntro
  | imod
  | isplit
  | applyHyps
  | custom
  deriving Inhabited, BEq, Hashable, Ord

namespace TacticDescr

instance : ToString TacticDescr where
  toString
    | .identity => "identity"
    | .icases => "icases"
    | .ipureIntro => "ipureIntro"
    | .ileft => "ileft"
    | .iright => "iright"
    | .iexist => "iexist"
    | .imodIntro => "imodIntro"
    | .imod => "imod"
    | .isplit => "isplit"
    | .applyHyps => "applyHyps"
    | .custom => "custom"

end TacticDescr

/- Rule Builder kind -/
inductive RuleBuilder where
  | «forward»
  | «backward»
  | «tactic» (descr : TacticDescr)
  deriving Inhabited, BEq, Hashable, Ord

namespace RuleBuilder

instance : ToString RuleBuilder where
  toString
    | «forward» => "forward"
    | «backward» => "backward"
    | «tactic» descr => s!"tactic {descr}"

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
