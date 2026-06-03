module

public meta import Iris.ProofMode.Aesop.Index.Types

public meta section

namespace Iris.ProofMode.Aesop

open Lean Meta Iris BI

namespace Rule.Backward

/- Peel Iris-level implications until the remaining expression is the theorem conclusion. -/
private partial def peelIrisConclusion? (e : Expr) : MetaM (Option Expr) := do
  let e ← instantiateMVars e
  let e := e.consumeMData
  if let some args := e.appM? ``BIBase.wand then
    match args.back? with
    | some target => peelIrisConclusion? target
    | none => return none
  else if let some args := e.appM? ``BIBase.imp then
    match args.back? with
    | some target => peelIrisConclusion? target
    | none => return none
  else
    return some e

/- Extract the Iris proposition proved by a theorem type, if it has a supported shape. -/
private partial def matchConclusion? (type : Expr) : MetaM (Option Expr) :=
  match Iris.ProofMode.parseIrisGoal? type with
  | some irisGoal => peelIrisConclusion? irisGoal.goal
  | none =>
    match type.consumeMData.appM? ``BIBase.Entails,
        type.consumeMData.appM? ``BIBase.EmpValid,
        type.consumeMData.appM? ``BIBase.BiEntails with
    | some args, _, _ | _, some args, _ | _, _, some args =>
      match args.back? with
      | some target => peelIrisConclusion? target
      | none => return none
    | none, none, none => return none

/- Instantiate a theorem declaration and all of its forall binders. -/
def instantiateTheorem (decl : Name) : MetaM (Expr × Array Expr × Expr) := do
  let value ← mkConstWithFreshMVarLevels decl
  let type ← instantiateMVars (← inferType value)
  let ⟨mvars, _, body⟩ ← forallMetaTelescope type
  return (mkAppN value mvars, mvars, ← instantiateMVars body)

/- Instantiate a backward theorem and index it by the Iris proposition it can prove. -/
def mkBackwardIndexingMode (decl : Name) : MetaM IndexingMode :=
  withoutModifyingState do
    let (_, _, body) ← instantiateTheorem decl
    let target? ← (show MetaM (Option Expr) from do
      match ← matchConclusion? body with
      | some target => return some target
      | none => matchConclusion? (← whnf body))
    let some target := target?
      | throwError m!"iaesop: cannot infer backward rule target for {decl}"
    IndexingMode.targetMatching target

end Rule.Backward

end Iris.ProofMode.Aesop
