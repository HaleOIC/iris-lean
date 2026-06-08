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

example [BI PROP] (P : PROP) : P ⊢ P := by
  -- iaesop baseline
  iaesop

-- Basic context split test
example [BI PROP] (P Q R : PROP) : P ∗ Q ∗ R ⊢ R ∗ Q ∗ P:= by
  iaesop baseline

-- Multiple context split test
example [BI PROP] [BIAffine PROP] (P Q R S T: PROP) :
    T -∗ P -∗ Q -∗ R -∗ S -∗ P ∗ Q ∗ R ∗ S := by
  iaesop baseline

example [BI PROP] [BIAffine PROP] (P Q R S : PROP) :
    P -∗ Q  -∗ (P -∗ Q -∗ R) -∗ (P -∗ R)  -∗ (Q -∗ P -∗ S) -∗ (Q -∗ S) -∗ (R ∗ S) := by
  iaesop baseline

/- Nested context split test -/
example [BI PROP] (P Q R S : PROP) :
    P -∗ Q -∗ R -∗ ((P ∗ Q) -∗ R -∗ S) -∗ S := by
  iaesop baseline

example [BI PROP] (P Q R S : PROP) :
    Q -∗ R -∗ (P -∗ Q -∗ S) -∗ (R ∗ (P -∗ S)) := by
  iaesop baseline

/-- Tests `iapply` with two wands and subgoals -/
@[iaesop forward 100% backward 100%]
example [BI PROP] (P Q : Nat → PROP) :
    (P 1 -∗ P 2 -∗ Q 1) ⊢ □ P 1 -∗ P 2 -∗ Q 1 := by
  iaesop baseline

/-- Tests `ispecialize` with named subgoal -/
@[iaesop backward 100%]
example [BI PROP] (Q : PROP) (φ : Prop) (hφ : φ):
    P ⊢ (⌜φ⌝ -∗ P -∗ ⌜True⌝ -∗ Q) -∗ Q := by
  iaesop baseline pureBy grind

/-- Tests `ispecialize` with mixed forall and wand specialization -/
-- A very useful example: we can identify the iprop in the target proposition
@[iaesop forward 100%]
example [BI PROP] (Q : Nat → PROP) :
    ⊢ □ P1 -∗ P2 -∗ (□ P1 -∗ (∀ x, P2 -∗ Q x)) -∗ Q y := by
  iaesop baseline

/- Tests `applyHyps` can parse Lean hypothesis to apply -/
example [BI PROP] (P Q : Nat → PROP) (H : ∀ x, ⊢ P x -∗ Q x) :
    P 1 -∗ Q 1 := by
  iaesop baseline

/-- Tests `iapply` with forall specialization -/
example [BI PROP] (P Q : α → PROP) (a b : α) :
    P a ∗ (∀ x, ∀ y, P x -∗ Q y) ⊢ Q b := by
  iaesop baseline

/-- One more example for iaesop, context refill -/
example [BI PROP] (P Q R : α → PROP) (a b c : α)
    (H : ⊢ ∀ x, ∀ y, ∀ z, P x -∗ Q y -∗ R z) : P a ∗ Q b ⊢ R c := by
  iaesop baseline

/-- Tests `iexact` with fupd -/
example [BI PROP] [BIUpdate PROP] [BIFUpdate PROP] [BIUpdateFUpdate PROP]
    (E : CoPset) (P : PROP) : P ⊢ |={E}=> P := by
  iaesop baseline

/-- Tests `iapply` with intuitionistic forall from Lean -/
example [BI PROP] (P Q : α → PROP) (a b : α) (H : ⊢ □ ∀ x, ∀ y, P x -∗ Q y) : P a ⊢ Q b := by
  iaesop baseline

example [BI PROP] [BIUpdate PROP] (P : PROP) : |==> |==> P ⊢ |==> P := by
  iaesop baseline

example [BI PROP] [BIAffine PROP] (P Q R S : PROP) :
    S -∗ (P ∨ Q) -∗ (P -∗ R) -∗ (Q -∗ S -∗ R) -∗ (Q -∗ R) -∗ (R ∗ S) := by
  iaesop baseline

example [BI PROP] (P Q : α → PROP) (R : PROP) :
    P a -∗ □ (∀ x, (P x -∗ Q x) ∧ R) -∗ Q a := by
  iaesop baseline

/-- Tests `iexists` with anonymous metavariable -/
example [BI PROP] : ⊢@{PROP} ∃ x, ⌜x = 42⌝ := by
  iaesop baseline pureBy grind

example [BI PROP] (P : α → PROP) : P a ⊢ ∃ x, P x := by
  iaesop baseline
