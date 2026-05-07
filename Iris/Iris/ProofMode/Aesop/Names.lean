module

public meta import Lean
public meta import Iris.ProofMode.Expr

public meta section

namespace Iris.ProofMode.Aesop

open Lean Meta Qq Std

public meta partial def hypNames : ∀ {prop : Q(Type u)} {bi : Q(BI $prop)} {e},
    Hyps bi e → NameSet
  | _, _, _, .emp _ => {}
  | _, _, _, .hyp _ name _ _ _ _ => {name}
  | _, _, _, .sep _ _ _ _ lhs rhs => hypNames lhs ∪ hypNames rhs

public meta def candidateName (pref : Name) (idx : Nat) : Name :=
  if idx == 0 then pref else pref.appendIndexAfter idx

public meta partial def firstUnusedName (used : NameSet) (pref : Name) (idx : Nat := 0) : Name :=
  let name := candidateName pref idx
  if used.contains name then firstUnusedName used pref (idx + 1) else name

public meta def freshIdent (used : NameSet) (pref : Name) : Ident :=
  mkIdent (firstUnusedName used pref)

public meta def freshIdent2 (used : NameSet) (pref1 pref2 : Name) : Ident × Ident :=
  let name1 := firstUnusedName used pref1
  let used := used.insert name1
  let name2 := firstUnusedName used pref2
  (mkIdent name1, mkIdent name2)

public meta def collectUsedNames (goal : MVarId) : MetaM NameSet := do
  goal.withContext do
    let mut used : NameSet := {}
    for localDecl in ← getLCtx do
      used := used.insert localDecl.userName
    if let some irisGoal := parseIrisGoal? (← goal.getType) then
      used := used ∪ hypNames irisGoal.hyps
    return used

public meta def freshIdentM (goal : MVarId) (pref : Name) : MetaM Ident := do
  return freshIdent (← collectUsedNames goal) pref

end Iris.ProofMode.Aesop
