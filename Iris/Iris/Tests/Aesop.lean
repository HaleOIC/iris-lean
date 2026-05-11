module

public import Iris.BI
public import Iris.ProofMode

@[expose] public section

namespace Iris.Tests
open Iris.BI

example [BI PROP] (P : PROP) : P ⊢ P := by
  iintro HP
  iaesop

example [BI PROP] (P Q : PROP) : P -∗ Q -∗ Q ∗ P := by
  iintro HP HQ
  iaesop

example [BI PROP] (P Q R S : PROP) : P -∗ Q -∗ R -∗ S -∗ P ∗ Q ∗ R ∗ S := by
  iintro HP HQ HR HS
  iaesop

/-- Tests `iapply` with two wands and subgoals -/
example [BI PROP] (P Q : Nat → PROP) :
  (P 1 -∗ P 2 -∗ Q 1) ⊢ □ P 1 -∗ P 2 -∗ Q 1 := by
  iintro H #HP1 HP2
  iapply H $$ [] [HP2]
  iaesop
  iaesop

/-- Tests `ispecialize` with named subgoal -/
example [BI PROP] (Q : PROP) : P ⊢ (⌜True⌝ -∗ P -∗ ⌜True⌝ -∗ Q) -∗ Q := by
  iintro HP HPQ
  ispecialize HPQ $$ [] [HP] []
  · ipure_intro; trivial
  · iexact HP
  · ipure_intro; trivial
  iexact HPQ

/-- Tests `ispecialize` with mixed forall and wand specialization -/
-- A very useful example: we can identify the iprop in the target proposition
example [BI PROP] (Q : Nat → PROP) :
    ⊢ □ P1 -∗ P2 -∗ (□ P1 -∗ (∀ x, P2 -∗ Q x)) -∗ Q y := by
  iintro #HP1 HP2 HPQ
  ispecialize HPQ $$ [] [HP2] <;> iaesop

/-- Tests `iapply` with forall specialization -/
example [BI PROP] (P Q : α → PROP) (a b : α) (H : ⊢ ∀ x, ∀ y, P x -∗ Q y) : P a ⊢ Q b := by
  iintro HP
  iapply H $$ [HP]
  iexact HP

/-- One more example for iaesop, context refill -/
example [BI PROP] (P Q R : α → PROP) (a b c : α) (H : ⊢ ∀ x, ∀ y, ∀ z, P x -∗ Q y -∗ R z) : P a ∗ Q b ⊢ R c := by
  iintro HPQ
  icases HPQ with ⟨HP, HQ⟩
  iapply H $$ [HP] [HQ]
  · iexact HP
  · iexact HQ

/-- Tests `iapply` with intuitionistic forall from Lean -/
example [BI PROP] (P Q : α → PROP) (a b : α) (H : ⊢ □ ∀ x, ∀ y, P x -∗ Q y) : P a ⊢ Q b := by
  iintro HP
  iaesop
  iapply H $$ [HP]
  iaesop
