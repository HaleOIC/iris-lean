module

public meta import Iris.ProofMode.Aesop.Tree.TreeM

public meta section

namespace Iris.ProofMode.Aesop

open Lean Meta Std

private def indent (n : Nat) : String :=
  String.ofList (List.replicate n ' ')

private def boolMark (b : Bool) : String :=
  if b then "true" else "false"

private def arrayToString (xs : Array String) : String :=
  "[" ++ String.intercalate ", " xs.toList ++ "]"

private def irisHypToString (hyp : IrisHyp) : String :=
  toString hyp.name

private def appliedHypToString : AppliedHyp → String
  | .spatial hyp => s!"spatial {irisHypToString hyp}"
  | .intuitionistic hyp => s!"intuitionistic {irisHypToString hyp}"
  | .lean userName _ => s!"lean {userName}"

private def usedHypToString : Option AppliedHyp → String
  | none => "none"
  | some hyp => appliedHypToString hyp

private def obunKindToString : ObunKind → String
  | .plain => "plain"
  | .managed => "managed"
  | .inherited source => s!"inherited from {source}"

private def normalizationStateToString : NormalizationState → String
  | .notNormal => "notNormal"
  | .normal goal .. => s!"normal {goal.name}"
  | .provenByNorm .. => "provenByNorm"

private def usedIrisHypsToString (state : GoalState) : String :=
  match state.usedIrisHyps? with
  | none => "[]"
  | some hyps => arrayToString (hyps.map irisHypToString)

private def maskToString (mask : ProgressMask) : String :=
  s!"{mask.mask.cpop.toNat}/{mask.n}"

private def currentGoalName (g : Goal) : String :=
  match g.normalizationState.normalizedGoal? with
  | some goal => toString goal.name
  | none => toString g.preNormGoal.name

mutual

private partial def renderObun (depth : Nat) (oref : ObunRef) :
    TreeM String := do
  let o ← oref.get
  let header :=
    s!"{indent depth}obun #{o.id} " ++
    s!"kind={obunKindToString o.kind} " ++
    s!"state={o.state} " ++
    s!"irrelevant={boolMark o.isIrrelevant} " ++
    s!"goals={o.goals.size} " ++
    s!"fullCtxGoals={o.fullContextIrisSubgoals.size}\n"
  let children ← o.goals.mapM (renderGoal (depth + 2))
  return header ++ String.join children.toList

private partial def renderGoal (depth : Nat) (gref : GoalRef) :
    TreeM String := do
  let g ← gref.get
  let header :=
    s!"{indent depth}goal #{g.id} " ++
    s!"state={g.state} " ++
    s!"origin={g.origin} " ++
    s!"mask={maskToString g.mask} " ++
    s!"depth={g.depth} " ++
    s!"irrelevant={boolMark g.isIrrelevant} " ++
    s!"norm={normalizationStateToString g.normalizationState} " ++
    s!"mvar={currentGoalName g} " ++
    s!"used={usedIrisHypsToString g.state} " ++
    s!"rapps={g.children.size}\n"
  let children ← g.children.mapM (renderRapp (depth + 2))
  return header ++ String.join children.toList

private partial def renderRapp (depth : Nat) (rref : RappRef) :
    TreeM String := do
  let r ← rref.get
  let header :=
    s!"{indent depth}rapp #{r.id} " ++
    s!"rule={r.appliedRule.info.builder} " ++
    s!"state={r.state} " ++
    s!"irrelevant={boolMark r.isIrrelevant} " ++
    s!"usedHyp={usedHypToString r.usedHyp?} " ++
    s!"splits={r.finalizedSpatialSplits.size} " ++
    s!"introducedMVars={r.introducedMVars.size} " ++
    s!"assignedMVars={r.assignedMVars.size}\n"
  let child ← renderObun (depth + 2) r.children
  return header ++ child

end

public meta def printSearchTreeBeforeFinalization : TreeM Unit := do
  let root ← getRootObun
  let iteration := (← readThe TreeM.Context).currentIteration
  let tree ← renderObun 0 root
  dbg_trace
    s!"\n[iaesop tree before finalization]\niteration={iteration}\n{tree}"

end Iris.ProofMode.Aesop
