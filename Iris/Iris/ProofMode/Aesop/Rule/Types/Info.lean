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
  | haveHyps
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
    | .haveHyps => "haveHyps"
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
  deriving Inhabited, BEq

namespace RuleInfo

protected def compare (rule₁ rule₂ : RuleInfo) : Ordering :=
  (compare rule₂.successProbability rule₁.successProbability).then
    (compare rule₁.builder rule₂.builder)

instance : Ord RuleInfo where
  compare := RuleInfo.compare

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
