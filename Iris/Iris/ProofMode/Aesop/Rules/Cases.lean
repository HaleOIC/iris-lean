module

public meta import Aesop
public import Iris.ProofMode.Aesop.Attr
public meta import Iris.ProofMode.Aesop.Names
public import Iris.ProofMode.Tactics.Cases
public import Iris.ProofMode.Tactics.ModIntro

namespace Iris.ProofMode.Aesop.Cases

open Lean Meta Qq Std Iris.ProofMode Aesop.RuleTac

/- Try to destruct ∗ in spatial context -/
private meta partial def findSep
    {prop : Q(Type u)} {bi : Q(BI $prop)} {e} (hyps : Hyps bi e)
    (used : NameSet) : MetaM (Option Syntax.Tactic) := do
  match hyps with
  | .emp _ => return none
  | .hyp _ name _ p A _ =>
    if isTrue p then return none
    if A.getAppFn.constName? != some ``Iris.BI.BIBase.sep then return none
    let (h1, h2) := freshIdent2 used `h1 `h2
    return some (← `(tactic| icases $(mkIdent name):ident with ⟨$h1:ident, $h2:ident⟩))
  | .sep _ _ _ _ lhs rhs =>
    if let some tac ← findSep lhs used then return some tac
    findSep rhs used

@[aesop norm -80 tactic (rule_sets := [iris])]
meta def iaesopCasesSep : Aesop.RuleTac := ofTacticSyntax λ input => do
  let tac? ← input.goal.withContext do
    let some irisGoal := parseIrisGoal? (← input.goal.getType)
      | throwError "iaesop cases: not an Iris proof-mode goal"
    findSep irisGoal.hyps $ ← collectUsedNames input
  let some tac := tac?
    | throwError "iaesop cases: no matching hypothesis shape"
  return tac

/- Try to destruct an existential proposition -/
private meta partial def findExists
    {prop : Q(Type u)} {bi : Q(BI $prop)} {e} (hyps : Hyps bi e)
    (used : NameSet) : MetaM (Option Syntax.Tactic) := do
  match hyps with
  | .emp _ => return none
  | .hyp _ name _ _ A _ =>
    if A.getAppFn.constName? != some ``Iris.BI.BIBase.exists then return none
    let x ← mkFreshLevelMVar
    let α : Q(Sort x) ← mkFreshExprMVarQ q(Sort x)
    let Φ : Q($α → $prop) ← mkFreshExprMVarQ q($α → $prop)
    match (← trySynthInstanceQ q(IntoExists $A $Φ)).toOption with
    | some _ =>
      let (x, h) := freshIdent2 used `x `h
      let xPat ← `(icasesPat| %$x:ident)
      let hPat ← `(icasesPat| $h:ident)
      return some (← `(tactic| icases $(mkIdent name):ident with ⟨$xPat:icasesPat, $hPat:icasesPat⟩))
    | none => return none
  | .sep _ _ _ _ lhs rhs =>
    if let some tac ← findExists lhs used then return some tac
    findExists rhs used

@[aesop norm -78 tactic (rule_sets := [iris])]
meta def iaesopCasesExists : Aesop.RuleTac := ofTacticSyntax λ input => do
  let tac? ← input.goal.withContext do
    let some irisGoal := parseIrisGoal? (← input.goal.getType)
      | throwError "iaesop cases: not an Iris proof-mode goal"
    findExists irisGoal.hyps $ ← collectUsedNames input
  let some tac := tac?
    | throwError "iaesop cases: no matching hypothesis shape"
  return tac

/- Try to destruct into pure proposition -/
private meta partial def findPure
    {prop : Q(Type u)} {bi : Q(BI $prop)} {e} (hyps : Hyps bi e)
    (used : NameSet) : MetaM (Option Syntax.Tactic) := do
  match hyps with
  | .emp _ => return none
  | .hyp _ name _ _ A _ =>
    let φ ← mkFreshExprMVarQ q(Prop)
    match (← trySynthInstanceQ q(IntoPure $A $φ)).toOption with
    | some _ =>
      let x := freshIdent used `x
      return (← `(tactic| icases $(mkIdent name):ident with %$x:ident))
    | none => return none
  | .sep _ _ _ _ lhs rhs =>
    if let some tac ← findPure lhs used then return some tac
    findPure rhs used

@[aesop norm -75 tactic (rule_sets := [iris])]
meta def iaesopCasesPure : Aesop.RuleTac := ofTacticSyntax λ input => do
  let tac? ← input.goal.withContext do
    let some irisGoal := parseIrisGoal? (← input.goal.getType)
      | throwError "iaesop cases: not an Iris proof-mode goal"
    findPure irisGoal.hyps $ ← collectUsedNames input
  let some tac := tac?
    | throwError "iaesop cases: no matching hypothesis shape"
  return tac

/- Try to destruct into intuitionistic propisiton-/
private meta partial def findIntuitionistic
    {prop : Q(Type u)} {bi : Q(BI $prop)} {e} (hyps : Hyps bi e)
    (used : NameSet) : MetaM (Option Syntax.Tactic) := do
  match hyps with
  | .emp _ => return none
  | .hyp _ name _ p A _ =>
    if isTrue p then return none
    let B ← mkFreshExprMVarQ q($prop)
    match (← trySynthInstanceQ q(IntoPersistently $p $A $B)).toOption with
    | some _ =>
      let h := freshIdent used `h
      return some (← `(tactic| icases $(mkIdent name):ident with #$h:ident))
    | none => return none
  | .sep _ _ _ _ lhs rhs =>
    if let some tac ← findIntuitionistic lhs used then return some tac
    findIntuitionistic rhs used

@[aesop norm -70 tactic (rule_sets := [iris])]
meta def iaesopCasesIntuitionistic : Aesop.RuleTac := ofTacticSyntax λ input => do
  let tac? ← input.goal.withContext do
    let some irisGoal := parseIrisGoal? (← input.goal.getType)
      | throwError "iaesop cases: not an Iris proof-mode goal"
    findIntuitionistic  irisGoal.hyps $ (← collectUsedNames input)
  let some tac := tac?
    | throwError "iaesop cases: no matching hypothesis shape"
  return tac

/- Try to destruct ∧ in intuitionistic context -/
private meta partial def findAnd
    {prop : Q(Type u)} {bi : Q(BI $prop)} {e} (hyps : Hyps bi e)
    (used : NameSet) : MetaM (Option Syntax.Tactic) := do
  match hyps with
  | .emp _ => return none
  | .hyp _ name _ p A _ =>
    -- if !isTrue p then return none
    let A1 ← mkFreshExprMVarQ q($prop)
    let A2 ← mkFreshExprMVarQ q($prop)
    match (← trySynthInstanceQ q(IntoAnd $p $A $A1 $A2)).toOption with
    | some _ =>
      let (h1, h2) := freshIdent2 used `h1 `h2
      return some (← `(tactic| icases $(mkIdent name):ident with ⟨$h1:ident, $h2:ident⟩))
    | none => return none
  | .sep _ _ _ _ lhs rhs =>
    if let some tac ← findAnd lhs used then return some tac
    findAnd rhs used

@[aesop norm -50 tactic (rule_sets := [iris])]
meta def iaesopCasesAnd : Aesop.RuleTac := ofTacticSyntax λ input => do
  let tac? ← input.goal.withContext do
    let some irisGoal := parseIrisGoal? (← input.goal.getType)
      | throwError "iaesop cases: not an Iris proof-mode goal"
    findAnd irisGoal.hyps $ ← collectUsedNames input
  let some tac := tac?
    | throwError "iaesop cases: no matching hypothesis shape"
  return tac

/- Try to destruct or into two branch (safe rules) -/
private meta partial def findOr
    {prop : Q(Type u)} {bi : Q(BI $prop)} {e} (hyps : Hyps bi e)
    (used : NameSet) : MetaM (Option Syntax.Tactic) := do
  match hyps with
  | .emp _ => return none
  | .hyp _ name _ _ A _ =>
    let A1 ← mkFreshExprMVarQ q($prop)
    let A2 ← mkFreshExprMVarQ q($prop)
    match (← trySynthInstanceQ q(IntoOr $A $A1 $A2)).toOption with
    | some _ =>
      let (h1, h2) := freshIdent2 used `h1 `h2
      return some (← `(tactic| icases $(mkIdent name):ident with ($h1:ident | $h2:ident)))
    | none => return none
  | .sep _ _ _ _ lhs rhs =>
    if let some tac ← findOr lhs used then return some tac
    findOr rhs used

@[aesop safe 20 tactic (rule_sets := [iris])]
meta def iaesopCasesOr : Aesop.RuleTac := ofTacticSyntax λ input => do
  let tac? ← input.goal.withContext do
    let some irisGoal := parseIrisGoal? (← input.goal.getType)
      | throwError "iaesop cases: not an Iris proof-mode goal"
    findOr irisGoal.hyps $ ← collectUsedNames input
  let some tac := tac?
    | throwError "iaesop cases: no matching hypothesis shape"
  return tac

/- Try to eliminate a modality from a hypothesis -/
private meta partial def findMod
    {prop : Q(Type u)} {bi : Q(BI $prop)} {e} (hyps : Hyps bi e)
    (goal : Q($prop)) : MetaM (Option Syntax.Tactic) := do
  match hyps with
  | .emp _ => return none
  | .hyp _ name _ p A _ =>
    let Φ : Q(Prop) ← mkFreshExprMVarQ q(Prop)
    let p' : Q(Bool) ← mkFreshExprMVarQ q(Bool)
    let A' : Q($prop) ← mkFreshExprMVarQ q($prop)
    let goal' : Q($prop) ← mkFreshExprMVarQ q($prop)
    match (← trySynthInstanceQ q(ElimModal $Φ $p $p' $A $A' $goal $goal')).toOption with
    | some _ =>
      return some (← `(tactic| imod $(mkIdent name):ident))
    | none => return none
  | .sep _ _ _ _ lhs rhs =>
    if let some tac ← findMod lhs goal then return some tac
    findMod rhs goal

@[aesop unsafe 10% tactic (rule_sets := [iris])]
meta def iaesopMod : Aesop.RuleTac := ofTacticSyntax λ input => do
  let tac? ← input.goal.withContext do
    let some irisGoal := parseIrisGoal? (← input.goal.getType)
      | throwError "iaesop imod: not an Iris proof-mode goal"
    findMod irisGoal.hyps irisGoal.goal
  let some tac := tac?
    | throwError "iaesop imod: no matching modal hypothesis"
  return tac

/- Try to introduce the modality in the goal -/
@[aesop unsafe 5% tactic (rule_sets := [iris])]
meta def iaesopModIntro : Aesop.RuleTac := ofTacticSyntax λ _ =>
  return Unhygienic.run `(tactic| imodintro)

end Iris.ProofMode.Aesop.Cases
