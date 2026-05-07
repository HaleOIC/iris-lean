module

public import Iris.ProofMode.Aesop.Tree.Data

public section

open Lean Lean.Meta Std

namespace Iris.ProofMode.Aesop.Tree

structure TreeSpec where
  Goal : Type
  Rapp : Type
  Obun : Type
  introGoal : GoalData (IO.Ref Rapp) (IO.Ref Obun) → Goal
  elimGoal : Goal → GoalData (IO.Ref Rapp) (IO.Ref Obun)
  introRapp : RappData (IO.Ref Goal) (IO.Ref Obun) → Rapp
  elimRapp : Rapp → RappData (IO.Ref Goal) (IO.Ref Obun)
  introObun : ObunData (IO.Ref Goal) (IO.Ref Rapp) → Obun
  elimObun : Obun → ObunData (IO.Ref Goal) (IO.Ref Rapp)

instance : Nonempty TreeSpec := by
  refine ⟨{
    Goal := Unit
    Rapp := Unit
    Obun := Unit
    introGoal := λ _ => ()
    elimGoal := λ _ => Classical.ofNonempty
    introRapp := λ _ => ()
    elimRapp := λ _ => Classical.ofNonempty
    introObun := λ _ => ()
    elimObun := λ _ => Classical.ofNonempty
  }⟩

mutual
  unsafe inductive GoalUnsafe where
    | mk : GoalData (IO.Ref RappUnsafe) (IO.Ref ObunUnsafe) → GoalUnsafe

  unsafe inductive RappUnsafe where
    | mk : RappData (IO.Ref GoalUnsafe) (IO.Ref ObunUnsafe) → RappUnsafe

  unsafe inductive ObunUnsafe where
    | mk : ObunData (IO.Ref GoalUnsafe) (IO.Ref RappUnsafe) → ObunUnsafe
end

unsafe def treeImpl : TreeSpec where
  Goal := GoalUnsafe
  Rapp := RappUnsafe
  Obun := ObunUnsafe
  introGoal := GoalUnsafe.mk
  elimGoal | GoalUnsafe.mk x => x
  introRapp := RappUnsafe.mk
  elimRapp | RappUnsafe.mk x => x
  introObun := ObunUnsafe.mk
  elimObun | ObunUnsafe.mk x => x

@[implemented_by treeImpl]
opaque tree : TreeSpec

public abbrev Goal := tree.Goal
public abbrev Rapp := tree.Rapp
public abbrev Obun := tree.Obun

public abbrev GoalRef   := IO.Ref Goal
public abbrev RappRef   := IO.Ref Rapp
public abbrev ObunRef   := IO.Ref Obun
public abbrev CtxSegRef := ObunRef
