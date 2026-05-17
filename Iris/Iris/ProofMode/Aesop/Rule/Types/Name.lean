module

public import Lean.Meta.Basic

public section

open Lean Lean.Meta

namespace Iris.ProofMode.Aesop

inductive RulePhase
  | norm
  | safe
  | «unsafe»
  deriving Inhabited, BEq, Hashable, Ord

namespace RulePhase

instance : ToString RulePhase where
  toString
    | norm => "norm"
    | safe => "safe"
    | «unsafe» => "unsafe"

end RulePhase

inductive RuleScope
  | global
  | «local»
  deriving Inhabited, BEq, Hashable, Ord

namespace RuleScope

instance : ToString RuleScope where
  toString
    | global => "global"
    | «local» => "local"

end RuleScope

-- TODO: extend to more building cases later (tactic?)
-- All only work in Iris-proofmode
inductive RuleBuilderKind
  | apply
  | forward
  | simp
  | unfold
  deriving Inhabited, BEq, Hashable, Ord

namespace RuleBuilderKind

instance : ToString RuleBuilderKind where
  toString
    | apply => "apply"
    | forward => "forward"
    | simp => "simp"
    | unfold => "unfold"

end RuleBuilderKind

-- [Warning] RuleId should be made unique within our rule sets
structure RuleId where
  name : Name
  kind : RuleBuilderKind
  phase : RulePhase
  scope : RuleScope
  deriving Inhabited, BEq, Hashable

namespace RuleId

protected def compare : RuleId → RuleId → Ordering :=
  compareLex (compareOn (·.kind)) $
  compareLex (compareOn (·.phase)) $
  compareLex (compareOn (·.scope)) $
  fun r₁ r₂ => r₁.name.cmp r₂.name

instance : Ord RuleId where
  compare := RuleId.compare

instance : ToString RuleId where
  toString r := s!"{r.phase}|{r.kind}|{r.scope}|{r.name}"

end RuleId

inductive DisplayRuleId
  | ruleId (id : RuleId)
  | normSimp
  | normUnfold
  deriving Inhabited, BEq, Hashable, Ord

namespace DisplayRuleId

instance : ToString DisplayRuleId where
  toString
    | ruleId n => toString n
    | normSimp => "<norm simp>"
    | normUnfold => "<norm unfold>"

end DisplayRuleId
