module

public meta import Lean
public meta import Iris.ProofMode.Expr
public meta import Iris.ProofMode.ProofModeM

public meta section

namespace Iris.ProofMode.Aesop

open Lean Meta Qq Std

public meta partial def hypNameArray : ∀ {prop : Q(Type u)} {bi : Q(BI $prop)} {e},
    Hyps bi e → Array Name
  | _, _, _, .emp _ => #[]
  | _, _, _, .hyp _ name _ _ _ _ => #[name]
  | _, _, _, .sep _ _ _ _ lhs rhs => hypNameArray lhs ++ hypNameArray rhs

public meta def collectIrisHypNames (goal : MVarId) : MetaM (Array Name) := do
  goal.withContext do
    let goalType ← instantiateMVars (← goal.getType)
    let some irisGoal := parseIrisGoal? goalType
      | return #[]
    return hypNameArray irisGoal.hyps

public meta def nameDepth? (name : Name) : Option Nat :=
  match name.eraseMacroScopes with
  | .str _ str =>
    match str.splitOn "_" with
    | depthPart :: indexPart :: [] =>
      match depthPart.dropPrefix? "H" with
      | some depthPart =>
        match depthPart.toNat?, indexPart.toNat? with
        | some depth, some _ => some depth
        | _, _ => none
      | none => none
    | _ => none
  | _ => none

/- Generate an unique binder name for search process -/
public meta def mkFreshBinderFromNames (names : Array Name) (depth : Nat)
    (offset : Nat := 1) :
    ProofModeM (TSyntax ``binderIdent) := do
  let index := names.foldl (init := 0) λ count name =>
    if nameDepth? name == some depth then count + 1 else count
  let ident := mkIdent $ (`H).appendAfter s!"{depth}_{index + offset}"
  `(binderIdent| $ident:ident)

end Iris.ProofMode.Aesop
