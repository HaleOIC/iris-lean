module

public meta import Iris.ProofMode.Aesop.Index.Types

public meta section

namespace Iris.ProofMode.Aesop

open Lean Meta Iris BI

namespace Rule.Backward

/- Peel Iris-level implications and universal binders until the remaining
expression is the theorem conclusion.  Backward rules are applied after these
binders have been introduced, so indexing a rule by the outer `∀` would make
it invisible when the actual target is its instantiated body. -/
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
  else if let some args := e.appM? ``BIBase.forall then
    let some body := args.back? | return none
    let bodyType ← whnf (← inferType body)
    let .forallE _ domain _ _ := bodyType | return none
    let value ← mkFreshExprMVar domain
    peelIrisConclusion? (mkApp body value).headBeta
  else
    return some e

/- Extract every Iris proposition by which a theorem should be indexed.  An
Iris equivalence is deliberately symmetric: registering `P ⊣⊢ Q` makes the
same backward theorem selectable for targets headed by either `P` or `Q`. -/
private partial def matchConclusions? (type : Expr) : MetaM (Option (Array Expr)) := do
  let type ← instantiateMVars type
  if let .forallE _ domain body _ := type then
    if ← Meta.isProp domain then
      let proof ← mkFreshExprMVar domain
      return ← matchConclusions? (body.instantiate1 proof)
  let type := type.consumeMData
  if let some args := type.appM? ``BIBase.BiEntails then
    let some left := args[args.size - 2]?
      | return none
    let some right := args.back?
      | return none
    let some left ← peelIrisConclusion? left | return none
    let some right ← peelIrisConclusion? right | return none
    return some #[left, right]
  match Iris.ProofMode.parseIrisGoal? type with
  | some irisGoal => return (← peelIrisConclusion? irisGoal.goal).map (#[·])
  | none =>
    match type.appM? ``BIBase.Entails, type.appM? ``BIBase.EmpValid with
    | some args, _ | _, some args =>
      let some target := args.back? | return none
      return (← peelIrisConclusion? target).map (#[·])
    | none, none => return none

/- Instantiate inference parameters, but preserve proposition-valued theorem
premises. `AsEmpValid` then translates a preserved Lean implication `φ → ψ`
into the Iris premise `⌜φ⌝ -∗ ψ`, so proof search sees and proves the premise
instead of leaving a hidden proof metavariable. -/
private partial def instantiateInferenceBinders (value type : Expr)
    (mvars : Array Expr := #[]) : MetaM (Expr × Array Expr × Expr) := do
  let type ← instantiateMVars type
  match type with
  | .forallE name domain body binderInfo =>
    if !binderInfo.isInstImplicit && (← Meta.isProp domain) then
      return (value, mvars, type)
    let kind := if binderInfo.isInstImplicit then MetavarKind.synthetic else .natural
    let mvar ← mkFreshExprMVar domain kind name
    instantiateInferenceBinders (mkApp value mvar) (body.instantiate1 mvar)
      (mvars.push mvar)
  | _ => return (value, mvars, type)

/- Instantiate a theorem declaration's inference binders while leaving its
ordinary proposition-valued premises visible to `AsEmpValid`. -/
def instantiateTheorem (decl : Name) : MetaM (Expr × Array Expr × Expr) := do
  let value ← mkConstWithFreshMVarLevels decl
  let type ← instantiateMVars (← inferType value)
  instantiateInferenceBinders value type

/- Instantiate a backward theorem and index it by the Iris proposition it can prove. -/
def mkBackwardIndexingMode (decl : Name) : MetaM IndexingMode :=
  withoutModifyingState do
    let (_, _, body) ← instantiateTheorem decl
    let targets? ← (show MetaM (Option (Array Expr)) from do
      match ← matchConclusions? body with
      | some targets => return some targets
      | none => matchConclusions? (← whnf body))
    let some targets := targets?
      | throwError m!"iaesop: cannot infer backward rule target for {decl}"
    let modes ← targets.mapM IndexingMode.targetMatching
    match modes with
    | #[mode] => return mode
    | _ => return .or modes

end Rule.Backward

end Iris.ProofMode.Aesop
