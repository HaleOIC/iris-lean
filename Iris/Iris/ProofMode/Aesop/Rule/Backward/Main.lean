module

public meta import Iris.ProofMode.Aesop.Frontend.Attribute
public meta import Iris.ProofMode.Aesop.Rule.Common.Main

public meta section

namespace Iris.ProofMode.Aesop

open Lean Meta Iris BI

initialize registerTraceClass `iaesop.ruleIndex

namespace Rule.Backward

/- Peel Iris-level implications until the remaining expression is the theorem conclusion -/
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

/- Extract the Iris proposition proved by a theorem type, if it has a supported shape -/
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

/- Instantiate a backward theorem and index it by the Iris proposition it can prove -/
private def mkBackwardIndexingMode (decl : Name) : MetaM IndexingMode :=
  withoutModifyingState do
    let value ← mkConstWithFreshMVarLevels decl
    let type ← instantiateMVars (← inferType value)
    let ⟨_, _, body⟩ ← forallMetaTelescope type
    let body ← instantiateMVars body
    let target? ← (show MetaM (Option Expr) from do
      match ← matchConclusion? body with
      | some target => return some target
      | none => matchConclusion? (← whnf body))
    let some target := target?
      | throwError m!"iaesop: cannot infer backward rule target for {decl}"
    IndexingMode.targetMatching target

end Rule.Backward

/- Build the discrimination-tree index for all registered backward rules -/
def backwardRuleIndex : MetaM (Index RuleInfo) := do
  let decls ← getIaesopBackwardLemmas
  let mut idx : Index RuleInfo := {}
  let mut entries : Array String := #[]
  for decl in decls do
    let indexingMode ← Rule.Backward.mkBackwardIndexingMode decl
    let rule : Rule RuleInfo := {
      id := {
        name := decl
        kind := .backward
        phase := .unsafe
        scope := .global
      }
      indexingMode
      info := RuleInfo.ofBuilder .backward
    }
    entries := entries.push s!"{decl}: {toString (format indexingMode)}"
    idx := idx.add rule rule.indexingMode
  trace[iaesop.ruleIndex] s!"iaesop.backward: generated backward index with {entries.size} rules"
  entries.forM λ entry => do
    trace[iaesop.ruleIndex] s!"  {entry}"
  return idx

end Iris.ProofMode.Aesop
