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

/- Optional pure Lean solver run after `ipureintro` exposes a pure goal. -/
declare_syntax_cat iaesopPureSolver
syntax "pureBy" tactic : iaesopPureSolver

syntax (name := iaesopTactic)  "iaesop"  (ppSpace iaesopStrategy)? (ppSpace iaesopNormMode)?
  (ppSpace iaesopRuleSet)? (ppSpace iaesopPureSolver)? : tactic
syntax (name := iaesopTactic?) "iaesop?" (ppSpace iaesopStrategy)? (ppSpace iaesopNormMode)?
  (ppSpace iaesopRuleSet)? (ppSpace iaesopPureSolver)? : tactic

end Iris.ProofMode.Aesop
