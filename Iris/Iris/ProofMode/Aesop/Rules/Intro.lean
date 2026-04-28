module

public import Aesop.Frontend
public import Iris.ProofMode.Aesop.Attr
public import Iris.ProofMode.Tactics.Intro

namespace Iris.ProofMode.Aesop.Intro

open Lean Qq Aesop.RuleTac Std

private meta partial def hypNames : ∀ {prop : Q(Type u)} {bi : Q(BI $prop)} {e},
    Hyps bi e → NameSet
  | _, _, _, .emp _ => {}
  | _, _, _, .hyp _ name _ _ _ _ => {name}
  | _, _, _, .sep _ _ _ _ lhs rhs => hypNames lhs ∪ hypNames rhs

private meta def candidateName (pref : Name) (idx : Nat) : Name :=
  if idx == 0 then pref else pref.appendIndexAfter idx

private meta partial def firstUnusedName (used : NameSet) (pref : Name) (idx : Nat := 0) : Name :=
  let name := candidateName pref idx
  if used.contains name then firstUnusedName used pref (idx + 1) else name

private meta def freshIdent (input : Aesop.RuleTacInput) (pref : Name) : MetaM Ident := do
  input.goal.withContext do
    let mut used : NameSet := {}
    for localDecl in ← getLCtx do
      used := used.insert localDecl.userName
    if let some irisGoal := parseIrisGoal? (← input.goal.getType) then
      used := used ∪ hypNames irisGoal.hyps
    return mkIdent (firstUnusedName used pref)

@[aesop norm -110 tactic (rule_sets := [iris])]
meta def iaesopIntroIntuinistic : Aesop.RuleTac := ofTacticSyntax λ input => do
  let h ← freshIdent input `h
  `(tactic| iintro #$h:ident)

@[aesop norm -100 tactic (rule_sets := [iris])]
meta def iaesopIntroPure : Aesop.RuleTac := ofTacticSyntax λ input => do
  let x ← freshIdent input `x
  `(tactic| iintro %$x:ident)

@[aesop norm -90 tactic (rule_sets := [iris])]
meta def iaesopIntro : Aesop.RuleTac := ofTacticSyntax λ input => do
  let h ← freshIdent input `h
  `(tactic| iintro $h:ident)

@[aesop norm -80 tactic (rule_sets := [iris])]
meta def iaesopIntroClear : Aesop.RuleTac := ofTacticSyntax λ _ => do
  `(tactic| iintro -)

end Iris.ProofMode.Aesop.Intro
