module

public meta import Iris.ProofMode.Aesop.Search.SearchM
public meta import Iris.ProofMode.Aesop.Tree.Print

public meta section

namespace Iris.ProofMode.Aesop.Search

open Lean Elab Tactic Meta Qq Std
open Iris.ProofMode

initialize registerTraceClass `iaesop.search.expand
initialize registerTraceClass `iaesop.search.replay

variable {Q : Type} [Queue Q]

private def findGoalById (oref : ObunRef) (id : GoalId) :
    SearchM Q (Option GoalRef) := do
  (← oref.get).goals.findM? λ gref => do
    return (← gref.get).id == id

private def formatLeanContext : MetaM String := do
  let mut lines := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then
      continue
    let tyFmt ← ppExpr (← instantiateMVars decl.type)
    lines := lines.push s!"{decl.userName} : {tyFmt.pretty}"
  if lines.isEmpty then
    return ""
  return lines.foldl (init := "\nLean context:") λ acc line => acc ++ "\n" ++ line

meta def traceSelectedGoal (gref : GoalRef) : SearchM Q Unit := do
  let g ← gref.get
  let caseIdx? := g.caseId?.map (·.toNat)
  let caseMsg := match caseIdx? with
    | some i => s!"case {i}"
    | none => "case ?"

  /- Already proven, no need to print -/
  if g.state.isProven || g.normalizationState.isProvenByNorm then
    trace[iaesop.search.expand] s!"iaesop.expand: selected goal {g.id}, {caseMsg}, \
        origin={g.origin}, state={g.state}, no active Iris goal"
    return

  let (goal, state) ← match g.normalizationState with
    | .normal postGoal postState .. =>
      pure (postGoal, postState)
    | .notNormal =>
      pure (g.preNormGoal, g.preNormState)
    | _ =>
      throwError "iaesop: unexpected normalization state during trace"

  let goalText ← liftM (m := MetaM) do
    let preState ← saveState
    state.restore
    let (goalFmt, _leanContext) ← goal.withContext do
      let goalType ← instantiateMVars (← goal.getType)
      let goalFmt ←
        match parseIrisGoal? goalType with
        | some irisGoal => ppExpr (IrisGoal.toExpr irisGoal)
        | none => ppExpr goalType
      return (goalFmt, ← formatLeanContext)
    preState.restore
    -- return _leanContext ++ goalFmt.pretty
    return goalFmt.pretty

  trace[iaesop.search.expand] s!"iaesop.expand: selected goal {g.id}, {caseMsg}, \
    origin={g.origin}, mask={repr g.mask}\n{goalText}"

meta def traceTreeBeforeReplay : SearchM Q Unit := do
  trace[iaesop.search.replay] ← printSearchTree

end Iris.ProofMode.Aesop.Search
