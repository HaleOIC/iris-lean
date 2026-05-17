module

public section

namespace Iris.ProofMode.Aesop

/- Specify strategy. -/
declare_syntax_cat iaesopStrategy
syntax "bestFirst" : iaesopStrategy
syntax "depthFirst" : iaesopStrategy
syntax "breadthFirst" : iaesopStrategy

/- Specify the normalization mode used by iaesop. -/
declare_syntax_cat iaesopNormMode
syntax "unfold" : iaesopNormMode
syntax "simp" : iaesopNormMode
syntax "normAll" : iaesopNormMode

/- Specify the rule set used by iaesop. -/
declare_syntax_cat iaesopRuleSet
syntax "builtin" : iaesopRuleSet
syntax "baseline" : iaesopRuleSet

syntax (name := iaesopTactic)  "iaesop"  (ppSpace iaesopStrategy)? (ppSpace iaesopNormMode)?
  (ppSpace iaesopRuleSet)? : tactic
syntax (name := iaesopTactic?) "iaesop?" (ppSpace iaesopStrategy)? (ppSpace iaesopNormMode)?
  (ppSpace iaesopRuleSet)? : tactic

end Iris.ProofMode.Aesop
