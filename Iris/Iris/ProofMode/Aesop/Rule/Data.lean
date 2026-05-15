module

public import Lean
public import Iris.ProofMode.Aesop.Rule.Types.Name
public import Iris.ProofMode.Aesop.Util.Basic

public section

namespace Iris.ProofMode.Aesop

open Lean

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

structure RuleName where
  name : Name
  phase : RulePhase
  builder : RuleBuilder
  deriving Inhabited, BEq, Hashable

namespace RuleName

protected def compare (r s : RuleName) : Ordering :=
  compare r.phase s.phase |>.then $
  compare r.builder s.builder |>.then $
  r.name.cmp s.name

instance : Ord RuleName where
  compare := RuleName.compare

instance : ToString RuleName where
  toString rule :=
    s!"{rule.phase}.{rule.builder}.{rule.name}"

instance : ToFormat RuleName where
  format rule := Std.Format.text (toString rule)

end RuleName

inductive RuleSafety where
  | safe
  | «unsafe»
  deriving Inhabited, BEq, Hashable, Ord

structure RegularRule where
  name : RuleName
  safety : RuleSafety
  successProbability : Percent
  deriving Inhabited, BEq, Ord

namespace RegularRule

instance : Hashable RegularRule where
  hash rule := hash rule.name

instance : ToFormat RegularRule where
  format rule := format rule.name

def isSafe (rule : RegularRule) : Bool :=
  rule.safety == .safe

def isUnsafe (rule : RegularRule) : Bool :=
  rule.safety == .unsafe

def mkSafe (name : RuleName) (successProbability : Percent := Percent.hundred) :
    RegularRule where
  name := name
  safety := .safe
  successProbability := successProbability

def mkUnsafe (name : RuleName) (successProbability : Percent := Percent.fifty) :
    RegularRule where
  name := name
  safety := .unsafe
  successProbability := successProbability

end RegularRule

end Iris.ProofMode.Aesop
