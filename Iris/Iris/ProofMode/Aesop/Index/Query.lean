module

public meta import Std.Data.TreeMap
public meta import Iris.ProofMode.Aesop.Index.Basic

public meta section

namespace Iris.ProofMode.Aesop.Index

open Lean Lean.Meta
open Iris.ProofMode

initialize registerTraceClass `iaesop.ruleIndex

variable {α : Type}

private abbrev HitMap (α : Type) [Ord α] :=
  Std.TreeMap (Rule α) (Array IndexMatchLocation)
    Rule.compareByPriorityThenName

private inductive QuerySurface
  | fullGoal (e : Expr)
  | target (e : Expr)
  | irisHyp (loc : IndexMatchLocation) (e : Expr)
  | leanHyp (loc : IndexMatchLocation) (e : Expr)
  | unindexed

private partial def collectIrisHyps {u prop bi} :
    ∀ {e}, @Hyps u prop bi e → Array (IndexMatchLocation × Expr)
  | _, .emp _ => #[]
  | _, .hyp _ name ivarId p type _ =>
    #[(
      .irisHyp name ivarId (isTrue p),
      type
    )]
  | _, .sep _ _ _ _ lhs rhs =>
    collectIrisHyps lhs ++ collectIrisHyps rhs

@[inline]
private def collectSurfaces (mvar : MVarId) (irisGoal : IrisGoal) :
    MetaM (Array QuerySurface) :=
  mvar.withContext do
    let mut surfaces : Array QuerySurface :=
      #[.fullGoal (← mvar.getType), .target irisGoal.goal]
    for (loc, hypType) in collectIrisHyps irisGoal.hyps do
      surfaces := surfaces.push (.irisHyp loc hypType)
    for localDecl in ← getLCtx do
      if localDecl.isImplementationDetail then
        continue
      surfaces := surfaces.push
        (.leanHyp (.leanHyp localDecl.userName localDecl.fvarId) localDecl.type)
    return surfaces.push .unindexed

@[inline]
private def locationsToSet (locs : Array IndexMatchLocation) :
    Std.HashSet IndexMatchLocation := Id.run do
  let mut result : Std.HashSet IndexMatchLocation := {}
  for loc in locs do
    result := result.insert loc
  return result

@[inline]
private def emptyHitMap [Ord α] : HitMap α :=
  Std.TreeMap.empty

@[inline]
private def insertHit [Ord α] (m : HitMap α) (rule : Rule α)
    (loc : IndexMatchLocation) : HitMap α :=
  match m.get? rule with
  | none => m.insert rule #[loc]
  | some locs => m.insert rule (locs.push loc)

@[inline]
private def collectIndexed [Ord α] (tree : DiscrTree (Rule α)) (e : Expr)
    (loc : IndexMatchLocation) (include? : Rule α → Bool)
    (m : HitMap α) : MetaM (HitMap α) := do
  let e ← instantiateMVars e
  let rules ← getUnify tree e
  return rules.foldl (init := m) λ m rule =>
    if include? rule then insertHit m rule loc else m

@[inline]
private def collectUnindexed [Ord α] (idx : Index α)
    (include? : Rule α → Bool) (m : HitMap α) : HitMap α := Id.run do
  let mut result := m
  for rule in idx.unindexed do
    if include? rule then
      result := insertHit result rule .none
  return result

@[inline]
private def collectSurface [Ord α] (idx : Index α)
    (include? : Rule α → Bool) (m : HitMap α) :
    QuerySurface → MetaM (HitMap α)
  | .fullGoal e => collectIndexed idx.byFullGoal e .fullGoal include? m
  | .target e => collectIndexed idx.byTarget e .target include? m
  | .irisHyp loc e => collectIndexed idx.byIrisHyp e loc include? m
  | .leanHyp loc e => collectIndexed idx.byLeanHyp e loc include? m
  | .unindexed => return collectUnindexed idx include? m

@[inline]
private def hitMapToResults [Ord α] (m : HitMap α) :
    Array (IndexMatchResult (Rule α)) :=
  let results := m.foldl
    (λ acc rule locations =>
      acc.push { rule, locations := locationsToSet locations })
    (init := Array.mkEmpty m.size)
  results.qsort λ r s =>
    Rule.compareByPriorityThenName r.rule s.rule == .lt

/-- Query an index against all matchable surfaces of an Iris proof-mode goal:
the full Lean goal type, the Iris target, Iris proof-mode hypotheses, Lean local
 hypotheses, and unindexed rules. -/
def query [Ord α]
    (idx : Index α) (mvar : MVarId) (irisGoal : IrisGoal)
    (include? : Rule α → Bool := λ _ => true) :
    MetaM (Array (IndexMatchResult (Rule α))) := do
  let mut result : HitMap α := emptyHitMap
  for surface in ← collectSurfaces mvar irisGoal do
    result ← collectSurface idx include? result surface
  return hitMapToResults result

def queryMVar [Ord α]
    (idx : Index α) (mvar : MVarId)
    (include? : Rule α → Bool := fun _ => true) :
    MetaM (Array (IndexMatchResult (Rule α))) := do
  mvar.withContext do
    let goalType ← instantiateMVars (← mvar.getType)
    let some irisGoal := parseIrisGoal? goalType
      | return #[]
    query idx mvar irisGoal include?

end Index

end Iris.ProofMode.Aesop
