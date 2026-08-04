module

public meta import Iris.ProofMode.Aesop.Rule.Backward.Shape
public meta import Iris.ProofMode.Aesop.Rule.Tactic.ApplyHyps
public import Iris.ProofMode.InstancesMake

public section

namespace Iris.ProofMode.Aesop.Rule.Backward

open Iris BI
open Iris.ProofMode

/- A Lean proposition parameter is affine proof information, not a spatial
resource.  Keep this conversion local to backward rules: changing the global
`AsEmpValid` instance would also change the semantics of `istart`. -/
theorem empValid_affinePure_wand [BI PROP] {φ : Prop} {P Q : PROP}
    [hA : MakeAffinely iprop(⌜φ⌝) P] [Affine P]
    (h : φ → ⊢ Q) : ⊢ P -∗ Q :=
  entails_wand <| pure_elim φ
    (hA.make_affinely.mpr.trans affinely_elim)
    (λ hp => Affine.affine.trans <| h hp)

theorem have_empValid [BI PROP] {P Q : PROP} (h : ⊢ P) : Q ⊢ Q ∗ □ P :=
  sep_emp.2.trans <| sep_mono_right <|
    intuitionistically_emp.2.trans <| intuitionistically_mono h

end Iris.ProofMode.Aesop.Rule.Backward

public meta section

namespace Iris.ProofMode.Aesop

open Lean Meta Qq Iris BI
open Iris.ProofMode

initialize registerTraceClass `iaesop.backward

namespace Rule.Backward

private structure BackwardExpansion where
  body : Expr
  goals : Array SubGoal
  fullContextIrisSubgoals : Array IrisGoal
  postState : SavedState

/- Convert a theorem value into the Iris proposition used by a backward rule.
Ordinary proposition-valued parameters are recursively exposed as affine pure
wand premises.  The terminal proposition still uses the ordinary
`AsEmpValid` bridge. -/
private partial def mkBackwardHypFromValue?
    {prop : Q(Type u)} (bi : Q(BI $prop)) (value type : Expr) :
    MetaM (Option ((hyp : Q($prop)) × Q(⊢ $hyp))) := do
  let type ← instantiateMVars type
  if let .forallE name domain body binderInfo := type then
    if ← Meta.isProp domain then
      have domain : Q(Prop) := domain
      return ← withLocalDecl name binderInfo domain fun hp => do
        let body := body.instantiate1 hp
        let some ⟨inner, innerProof⟩ ←
            mkBackwardHypFromValue? bi (mkApp value hp) body
          | return none
        if inner.containsFVar hp.fvarId! then return none
        let innerProofFn ← mkLambdaFVars #[hp] innerProof
        have innerProofFn : Q($domain → ⊢ $inner) := innerProofFn
        let premise ← mkFreshExprMVarQ prop
        let .some (hA, _) ← trySynthInstanceProbeQ
            q(MakeAffinely iprop(⌜$domain⌝) $premise)
          | return none
        let premise : Q($prop) ← instantiateMVars premise
        let hA : Q(MakeAffinely iprop(⌜$domain⌝) $premise) := hA
        let .some (hAffine, _) ← trySynthInstanceProbeQ q(Affine $premise)
          | return none
        let _hAffine : Q(Affine $premise) := hAffine
        let hyp : Q($prop) := q(iprop($premise -∗ $inner))
        let proof : Q(⊢ $hyp) :=
          q(empValid_affinePure_wand (hA := $hA) (h := $innerProofFn))
        return some ⟨hyp, proof⟩
  if !(← Meta.isProp type) then return none
  have type : Q(Prop) := type
  have value : Q($type) := value
  let hyp ← mkFreshExprMVarQ prop
  let .some (inst, _) ← trySynthInstanceProbeQ
      q(AsEmpValid .into $type .in $prop .in $bi $hyp)
    | return none
  let hyp : Q($prop) ← instantiateMVars hyp
  let _inst : Q(AsEmpValid .into $type .in $prop .in $bi $hyp) := inst
  return some ⟨hyp, q(asEmpValid_1 $hyp $value)⟩

/-- Bridge a theorem proof into the current Iris BI as an intuitionistic proposition. -/
private def mkBackwardHyp? {prop : Q(Type u)} (bi : Q(BI $prop))
    (decl : Name) : MetaM (Option (Q($prop) × Expr)) := do
  let (value, _, body) ← instantiateTheorem decl
  let some ⟨hyp, _⟩ ← mkBackwardHypFromValue? bi value body
    | trace[iaesop.backward] "backward rejected {decl}: cannot convert theorem parameters"
      return none
  return some (hyp, ← instantiateMVars body)

/-- Build a search expansion when a backward theorem directly proves the target. -/
private def mkCloseExpansion?
    {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)}
    (hyp target : Q($prop)) (body : Expr) : MetaM (Option BackwardExpansion) := do
  let hyp : Q($prop) ← instantiateMVars hyp
  let target : Q($prop) ← instantiateMVars target
  let preState ← saveState
  match ← trySynthInstanceProbeQ q(FromAssumption true .in $hyp $target) with
  | .none | .undef => preState.restore; return none
  | .some _ =>
    let _ := ← instantiateMVars hyp
    let _ := ← instantiateMVars target
    return some {
      body,
      goals := #[],
      fullContextIrisSubgoals := #[],
      postState := ← saveState
    }

/-- Build a search expansion by applying a backward theorem to the current target. -/
private def mkExpansion? (decl : Name) (irisGoal : IrisGoal) (tag : Name)
    (baseState : SavedState) : MetaM (Option BackwardExpansion) := do
  let { bi, goal := target, .. } := irisGoal
  baseState.restore
  let some (hyp, body) ← mkBackwardHyp? bi decl
    | return none
  let bridgedState ← saveState
  if let some expansion ← mkCloseExpansion? (bi := bi) hyp target body then
    return some expansion
  bridgedState.restore
  let some premises ← Rule.ApplyHyps.collectApplyPremises? (bi := bi) q(true) hyp target
    | baseState.restore; return none
  let (goals, fullContextIrisSubgoals) ←
    Rule.ApplyHyps.mkChildren irisGoal tag irisGoal.hyps premises
  return some { body, goals, fullContextIrisSubgoals, postState := ← saveState }

/-- Search stage work for a registered backward theorem. -/
def run {Q : Type} [Queue Q] (input : RuleInput) : CoreM Q RuleOutput := do
  let decl := input.matchResult.rule.id.name
  let expansion? ← liftM do
    restoreState input.state
    input.goal.withContext do
      let goalType ← instantiateMVars (← input.goal.getType)
      let some irisGoal := parseIrisGoal? goalType
        | throwError "iaesop: backward rule search must work in iris proof-mode context"
      mkExpansion? decl irisGoal (← input.goal.getTag) (← saveState)
  let some expansion := expansion?
    | return {}
  trace[iaesop.backward] s!"backward selected {decl}"
  let bodyFmt ← liftM <| ppExpr expansion.body
  trace[iaesop.backward] s!"backward selected body: {bodyFmt.pretty}"
  return RuleOutput.ofRappSpec {
    goals := expansion.goals
    postState := expansion.postState
    successPossibility := ⟨0.6⟩
    effect := {
      action :=
        if expansion.goals.isEmpty then some .closeGoal
        else if expansion.goals.size == 1 then none
        else some (.manageContext expansion.fullContextIrisSubgoals)
    }
  }

/-- Synthesize the backward theorem's instance-argument metavariables. -/
private def synthAuxInstances (mvars : Array Expr) : MetaM Unit := do
  for mvarExpr in mvars do
    let .mvar mvarId := ← instantiateMVars mvarExpr | continue
    if ← mvarId.isAssigned then continue
    let mvarType ← instantiateMVars (← mvarId.getType)
    let some _ ← isClass? mvarType | continue
    let some inst ← synthInstance? mvarType | continue
    mvarId.assign inst

/-- Replay a registered backward theorem as an Iris intuitionistic proposition -/
private def mkBackwardProof {prop : Q(Type u)} {bi : Q(BI $prop)} {e : Q($prop)}
    (decl : Name) : ProofModeM ((hyp : Q($prop)) × Q($e ⊢ $e ∗ □ $hyp) × Array Expr) := do
  let (value, mvars, body) ← instantiateTheorem decl
  let some ⟨hyp, proof⟩ ← mkBackwardHypFromValue? bi value body
    | throwError m!"iaesop(baseline): backward replay cannot bridge theorem {decl} into Iris"
  return ⟨hyp, q(have_empValid (Q := $e) $proof), mvars⟩

/-- Replay a close-goal backward theorem application. -/
private def replayClose (decl : Name) (goalMVarId : MVarId) :
    ProofModeM (Array MVarId) := do
  goalMVarId.withContext do
    let goalType ← instantiateMVars (← goalMVarId.getType)
    let some { bi, e, goal := target, .. } := parseIrisGoal? goalType
      | throwError "iaesop(baseline): backward replay expected an Iris goal"
    let ⟨hyp, haveProof, mvars⟩ ← mkBackwardProof (bi := bi) (e := e) decl
    let coreProof ← Rule.ApplyHyps.mkCloseCoreProof (bi := bi) (e := e) q(true) hyp target
    synthAuxInstances mvars
    goalMVarId.assign q(Entails.trans $haveProof $coreProof)
    return #[]

/-- Replay a backward theorem application that generated premise subgoals. -/
private def replayApply (decl : Name) (goalMVarId : MVarId)
    (contexts : Array (Array IrisHyp)) : ProofModeM (Array MVarId) := do
  goalMVarId.withContext do
    let goalType ← instantiateMVars (← goalMVarId.getType)
    let some { bi, e, hyps, goal := target, .. } := parseIrisGoal? goalType
      | throwError "iaesop(baseline): backward replay expected an Iris goal"
    let ⟨hyp, haveProof, mvars⟩ ← mkBackwardProof (bi := bi) (e := e) decl
    let (coreProof, goals) ←
      Rule.ApplyHyps.replayApplyCore (bi := bi) hyps q(true) hyp target contexts (← goalMVarId.getTag)
    synthAuxInstances mvars
    goalMVarId.assign q(Entails.trans $haveProof $coreProof)
    return goals

/-- Replay stage work for a registered backward theorem. -/
def replay (input : RuleReplayInput) : ProofModeM (Array MVarId) := do
  let decl := input.rapp.appliedRule.id.name
  let obun ← input.rapp.children.get
  if obun.goals.isEmpty || obun.kind.isInherited then
    replayClose decl input.goal
  else if obun.goals.size == 1 then
    if !obun.finalizedSpatialSplits.isEmpty then
      throwError "iaesop(baseline): backward replay found finalized spatial splits for a single-premise apply; expected no split information"
    replayApply decl input.goal #[]
  else
    if obun.finalizedSpatialSplits.size != obun.goals.size then
      throwError s!"iaesop(baseline): backward replay found {obun.finalizedSpatialSplits.size} finalized spatial splits for {obun.goals.size} generated goals"
    replayApply decl input.goal obun.finalizedSpatialSplits

end Rule.Backward

end Iris.ProofMode.Aesop
