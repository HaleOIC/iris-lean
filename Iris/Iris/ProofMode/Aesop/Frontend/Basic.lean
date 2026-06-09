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

/- Local rule edits for one `iaesop` invocation. -/
declare_syntax_cat iaesopRuleDirection
syntax "backward" : iaesopRuleDirection
syntax "forward" : iaesopRuleDirection

declare_syntax_cat iaesopLocalRule
syntax iaesopRuleDirection ppSpace ident (ppSpace num "%")? : iaesopLocalRule

declare_syntax_cat iaesopErasedRule
syntax iaesopRuleDirection ppSpace ident : iaesopErasedRule

declare_syntax_cat iaesopRuleEdit
syntax "with" "[" iaesopLocalRule,* "]" : iaesopRuleEdit
syntax "without" "[" iaesopErasedRule,* "]" : iaesopRuleEdit

syntax (name := iaesopTactic)  "iaesop"  (ppSpace iaesopStrategy)? (ppSpace iaesopNormMode)?
  (ppSpace iaesopRuleSet)? (ppSpace iaesopPureSolver)? (ppSpace iaesopRuleEdit)* : tactic
syntax (name := iaesopTactic?) "iaesop?" (ppSpace iaesopStrategy)? (ppSpace iaesopNormMode)?
  (ppSpace iaesopRuleSet)? (ppSpace iaesopPureSolver)? (ppSpace iaesopRuleEdit)* : tactic

end Iris.ProofMode.Aesop
