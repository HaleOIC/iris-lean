module

public import Iris.ProofMode.Tactics.Intro
public import Aesop.Frontend
public import Iris.ProofMode.Aesop.Attr
public meta import Iris.ProofMode.Aesop.Names

namespace Iris.ProofMode.Aesop.Intro

open Lean Qq Aesop.RuleTac Std

-- TODO: discuss the essence of the following intro rules
-- @[aesop norm -110 tactic (rule_sets := [iris])]
-- meta def iaesopIntroIntuinistic : Aesop.RuleTac := ofTacticSyntax λ input => do
--   let h ← freshIdentM input `h
--   `(tactic| iintro #$h:ident)

@[aesop norm -100 tactic (rule_sets := [iris])]
meta def iaesopIntroPure : Aesop.RuleTac := ofTacticSyntax λ input => do
  let x ← freshIdentM input `x
  `(tactic| iintro %$x:ident)

@[aesop norm -90 tactic (rule_sets := [iris])]
meta def iaesopIntro : Aesop.RuleTac := ofTacticSyntax λ input => do
  let h ← freshIdentM input `h
  `(tactic| iintro $h:ident)

@[aesop norm -80 tactic (rule_sets := [iris])]
meta def iaesopIntroClear : Aesop.RuleTac := ofTacticSyntax λ _ => do
  `(tactic| iintro -)

end Iris.ProofMode.Aesop.Intro
