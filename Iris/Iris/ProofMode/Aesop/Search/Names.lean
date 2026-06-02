module

public meta import Lean
public meta import Iris.ProofMode.Expr
public meta import Iris.ProofMode.ProofModeM

public meta section

namespace Iris.ProofMode.Aesop

open Lean Meta Qq Std
open Iris.BI

public meta partial def hypNameArray : ∀ {prop : Q(Type u)} {bi : Q(BI $prop)} {e},
    Hyps bi e → Array Name
  | _, _, _, .emp _ => #[]
  | _, _, _, .hyp _ name _ _ _ _ => #[name]
  | _, _, _, .sep _ _ _ _ lhs rhs => hypNameArray lhs ++ hypNameArray rhs

/- Collect spatial Iris hypotheses as `(name, ivar, type)` triples. -/
public meta partial def spatialHypEntries :
    ∀ {prop : Q(Type u)} {bi : Q(BI $prop)} {e},
      Hyps bi e → Array (Name × IVarId × Expr)
  | _, _, _, .emp _ => #[]
  | _, _, _, .hyp _ name ivar p ty _ =>
    if isTrue p then #[] else #[(name, ivar, ty)]
  | _, _, _, .sep _ _ _ _ lhs rhs =>
    spatialHypEntries lhs ++ spatialHypEntries rhs

public meta def collectIrisHypNames (goal : MVarId) : MetaM (Array Name) := do
  goal.withContext do
    let goalType ← instantiateMVars (← goal.getType)
    let some irisGoal := parseIrisGoal? goalType
      | return #[]
    return hypNameArray irisGoal.hyps

public meta def nameDepthWithPrefix? (pref : String) (name : Name) : Option Nat :=
  match name.eraseMacroScopes with
  | .str _ str =>
    match str.splitOn "_" with
    | depthPart :: indexPart :: [] =>
      match depthPart.dropPrefix? pref with
      | some depthPart =>
        match depthPart.toNat?, indexPart.toNat? with
        | some depth, some _ => some depth
        | _, _ => none
      | none => none
    | _ => none
  | _ => none

public meta def nameDepth? (name : Name) : Option Nat :=
  nameDepthWithPrefix? "H" name

/- Generate a unique binder name for search process. -/
public meta def mkFreshBinderFromNamesWithPrefix
    (pref : String) (names : Array Name) (depth : Nat)
    (offset : Nat := 1) :
    ProofModeM (TSyntax ``binderIdent) := do
  let index := names.foldl (init := 0) λ count name =>
    if nameDepthWithPrefix? pref name == some depth then count + 1 else count
  let ident := mkIdent $ (Name.mkSimple pref).appendAfter s!"{depth}_{index + offset}"
  `(binderIdent| $ident:ident)

/- Generate an unique Iris hypothesis binder name for search process. -/
public meta def mkFreshBinderFromNames (names : Array Name) (depth : Nat)
    (offset : Nat := 1) :
    ProofModeM (TSyntax ``binderIdent) :=
  mkFreshBinderFromNamesWithPrefix "H" names depth offset

/- Generate a Lean local binder name for pure introductions during normalization. -/
public meta def mkFreshLeanBinderFromNames (names : Array Name) (depth : Nat)
    (offset : Nat := 1) :
    ProofModeM (TSyntax ``binderIdent) :=
  mkFreshBinderFromNamesWithPrefix "h" names depth offset

public meta def mkBinderFromName (name : Name) :
    ProofModeM (TSyntax ``binderIdent) := do
  let ident := mkIdent name.eraseMacroScopes
  `(binderIdent| $ident:ident)

public meta def forallBinderName? (target : Expr) : Option Name := do
  let target := target.consumeMData
  if target.getAppFn.constName? != some ``BIBase.forall then
    none
  let some arg := target.getAppArgs.back?
    | none
  match arg.consumeMData with
  | .lam name .. =>
    match name.eraseMacroScopes with
    | .anonymous => none
    | name => some name
  | _ => none

end Iris.ProofMode.Aesop
