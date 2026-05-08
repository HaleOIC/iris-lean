module

public meta import Iris.ProofMode.Aesop.Index.Types
public meta import Iris.ProofMode.Aesop.Rule.Basic

public meta section

open Lean Lean.Meta

namespace Iris.ProofMode.Aesop

structure Index (α : Type) where
  byFullGoal : DiscrTree (Rule α)
  byTarget : DiscrTree (Rule α)
  byIrisHyp : DiscrTree (Rule α)
  byLeanHyp : DiscrTree (Rule α)
  unindexed : Std.HashSet (Rule α)
  deriving Inhabited

namespace Index

variable {α : Type} [BEq α] [Ord α] [Hashable α]

instance : EmptyCollection (Index α) where
  emptyCollection := {
    byFullGoal := {}
    byTarget := {}
    byIrisHyp := {}
    byLeanHyp := {}
    unindexed := {}
  }

def merge (rilhs rirhs : Index α) : Index α where
  byFullGoal := rilhs.byFullGoal.mergePreservingDuplicates rirhs.byFullGoal
  byTarget := rilhs.byTarget.mergePreservingDuplicates rirhs.byTarget
  byIrisHyp := rilhs.byIrisHyp.mergePreservingDuplicates rirhs.byIrisHyp
  byLeanHyp := rilhs.byLeanHyp.mergePreservingDuplicates rirhs.byLeanHyp
  unindexed := rilhs.unindexed.union rirhs.unindexed

partial def add (rule : Rule α) (mode : IndexingMode) (idx : Index α) :
    Index α :=
  match mode with
  | .unindexed =>
    { idx with unindexed := idx.unindexed.insert rule }
  | .fullGoal keys =>
    { idx with byFullGoal := idx.byFullGoal.insertKeyValue keys rule }
  | .target keys =>
    { idx with byTarget := idx.byTarget.insertKeyValue keys rule }
  | .irisHyps keys =>
    { idx with byIrisHyp := idx.byIrisHyp.insertKeyValue keys rule }
  | .leanHyps keys =>
    { idx with byLeanHyp := idx.byLeanHyp.insertKeyValue keys rule }
  | .or modes =>
    modes.foldl (init := idx) λ idx mode => idx.add rule mode

end Index

end Iris.ProofMode.Aesop
