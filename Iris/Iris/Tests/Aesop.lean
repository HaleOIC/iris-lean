module

public import Iris.BI
public import Iris.ProofMode

@[expose] public section

namespace Iris.Tests
open Iris.BI

-- Identity test
example [BI PROP] (P : PROP) : P ⊢ P := by
  iaesop

example [BI PROP] (P : PROP) : P ⊢ P := by
  iaesop bestFirst

example [BI PROP] (P : PROP) : P ⊢ P := by
  iaesop depthFirst

example [BI PROP] (P : PROP) : P ⊢ P := by
  iaesop breadthFirst

example [BI PROP] (P : PROP) : P ⊢ P := by
  iaesop simp

example [BI PROP] (P : PROP) : P ⊢ P := by
  iaesop depthFirst unfold

example [BI PROP] (P : PROP) : P ⊢ P := by
  iaesop breadthFirst normAll

-- Basic context split test
example [BI PROP] (P Q : PROP) : P ∗ Q ⊢ Q ∗ P := by
  iaesop

-- Multiple context split test
example [BI PROP] [BIAffine PROP] (P Q R S T: PROP) :
    T -∗ P -∗ Q -∗ R -∗ S -∗ P ∗ Q ∗ R ∗ S := by
  iaesop

example [BI PROP] [BIAffine PROP] (P Q R S : PROP) :
    P -∗ Q -∗ (P -∗ R) -∗ (P -∗ Q -∗ R)  -∗ (Q -∗ S) -∗ (Q -∗ P -∗ S) -∗ (R ∗ S) := by
  iaesop
  -- isplitl [HP Hwand2]
  -- · iapply Hwand2
  --   iexact HP
  -- · iapply Hwand3
  --   iexact HQ

/-- Tests `iapply` with two wands and subgoals -/
example [BI PROP] (P Q : Nat → PROP) :
  (P 1 -∗ P 2 -∗ Q 1) ⊢ □ P 1 -∗ P 2 -∗ Q 1 := by
  iaesop
  -- iapply H $$ [] [HP2]
  -- iaesop
  -- iaesop

/-- Tests `ispecialize` with named subgoal -/
example [BI PROP] (Q : PROP) (φ : Prop) (hφ : φ): P ⊢ (⌜φ⌝ -∗ P -∗ ⌜True⌝ -∗ Q) -∗ Q := by
  iaesop


/-- Tests `ispecialize` with mixed forall and wand specialization -/
-- A very useful example: we can identify the iprop in the target proposition
example [BI PROP] (Q : Nat → PROP) :
    ⊢ □ P1 -∗ P2 -∗ (□ P1 -∗ (∀ x, P2 -∗ Q x)) -∗ Q y := by
  iintro #HP1 HP2 HPQ
  ispecialize HPQ $$ [] [HP2] <;> iaesop

/-- Tests `iapply` with forall specialization -/
example [BI PROP] (P Q : α → PROP) (a b : α) :
  P a ∗ (∀ x, ∀ y, P x -∗ Q y) ⊢ Q b := by
  iaesop
  -- iapply H $$ [HP]
  -- iexact HP

/-- One more example for iaesop, context refill -/
example [BI PROP] (P Q R : α → PROP) (a b c : α) (H : ⊢ ∀ x, ∀ y, ∀ z, P x -∗ Q y -∗ R z) : P a ∗ Q b ⊢ R c := by
  iaesop
  -- iapply H $$ [HP] [HQ]
  -- · iexact HP
  -- · iexact HQ

/-- Tests `iexact` with fupd -/
example [BI PROP] [BIUpdate PROP] [BIFUpdate PROP] [BIUpdateFUpdate PROP]
    (E : CoPset) (P : PROP) : P ⊢ |={E}=> P := by
  iaesop

example [BI PROP] (φ : Prop) (hφ : φ) : ⊢ (⌜φ⌝ : PROP) := by
  iaesop

example [BI PROP] [BIUpdate PROP] (P : PROP) : P ⊢ |==> P := by
  iaesop

example [BI PROP] [BIUpdate PROP] (P : PROP) : |==> P ⊢ |==> P := by
  iaesop

example [BI PROP] (P Q R : PROP) : □ P ∗ □ Q ⊢ R -∗ R := by
  iaesop

/-- Tests `iapply` with intuitionistic forall from Lean -/
example [BI PROP] (P Q : α → PROP) (a b : α) (H : ⊢ □ ∀ x, ∀ y, P x -∗ Q y) : P a ⊢ Q b := by
  iaesop

example [BI PROP] [BIFUpdate PROP]
    (E1 E2 : CoPset) (P Q R : PROP) :
    (|={E1,E2}=> P ∗ Q ∗ R) ⊢ |={E1,E2}=> (P ∗ Q ∗ R) := by
  iaesop

example [BI PROP] [BIFUpdate PROP]
    (E : CoPset) (P : PROP) : □ (|={E}=> P) ⊢ |={E}=> P := by
  iaesop

example [BI PROP] [BIUpdate PROP] (P : PROP) : |==> |==> P ⊢ |==> P := by
  iaesop

example [BI PROP] [BIUpdate PROP] [BIFUpdate PROP] (P : PROP) [BIAffine PROP] E :
  P ⊢ ▷ |==> |={E}=> P := by
  iaesop

-- example [BI PROP] [BIAffine PROP] (P Q R S : PROP) :
--     S -∗ (P ∨ Q) -∗ (P -∗ R) -∗ (Q -∗ S -∗ R) -∗ (Q -∗ R) -∗ (R ∗ S) := by
--   iintro HS HPQ Hwand1 Hwand2 Hwand3
--   icases HPQ with ⟨HP | HQ⟩
--   · iframe; iapply Hwand1 $$ HP
--   · iframe; iapply Hwand3 $$ HQ

-- /-- Tests `iexists` with anonymous metavariable -/
-- example [BI PROP] : ⊢@{PROP} ∃ x, ⌜x = 42⌝ := by
--   iexists _
--   ipure_intro
--   rfl
