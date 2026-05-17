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

syntax (name := iaesopTactic)  "iaesop"  (ppSpace iaesopStrategy)? (ppSpace iaesopNormMode)? : tactic
syntax (name := iaesopTactic?) "iaesop?" (ppSpace iaesopStrategy)? (ppSpace iaesopNormMode)? : tactic

end Iris.ProofMode.Aesop
