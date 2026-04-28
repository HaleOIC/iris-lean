module

public import Iris.BI
public import Iris.ProofMode

@[expose] public section

namespace Iris.Tests
open Iris.BI

namespace normalization.intro

namespace intro

/-- Tests introducing a spatial hypothesis -/
example [BI PROP] (Q : PROP) : Q ⊢ Q := by
  iaesop?
  -- iintro HQ
  -- iexact HQ

/-- Tests introducing an intuitionistic hypothesis with the `#` pattern -/
example [BI PROP] (Q : PROP) : □ Q ⊢ Q := by
  iaesop?
  -- iintro #HQ
  -- iexact HQ

/-- Tests introducing an affine persistent proposition as intuitionistic -/
example [BI PROP] (Q : PROP) : <affine> <pers> Q ⊢ Q := by
  iaesop?
  -- iintro #HQ
  -- iexact HQ

/-- Tests introducing a persistent implication in the spatial context -/
example [BI PROP] (Q : PROP) : ⊢ <pers> Q → Q := by
  iaesop?
  -- iintro HQ
  -- iexact HQ


/- Tests introducing an implication in an intuitionistic context -/
example [BI PROP] (P : PROP) : ⊢ □ P -∗ P → P := by
  iaesop?
  -- iintro #HP1 HP2
  -- iexact HP2

/-- Tests dropping a hypothesis in an implication with the `-` pattern -/
example [BI PROP] (Q : PROP) : ⊢ P → Q -∗ Q := by
  iaesop?
  -- iintro - HQ
  -- iexact HQ

/-- Tests dropping a hypothesis in an implication in a non-empty context -/
example [BI PROP] (Q : PROP) : ⊢ Q -∗ P → Q := by
  iaesop?
  -- iintro HQ -
  -- iexact HQ

/-- Tests introducing an universally quantified variable -/
example [BI PROP] : ⊢@{PROP} ∀ x, ⌜x = 0⌝ → ⌜x = 0⌝ := by
  iaesop?
  -- iintro %x
  -- iintro H
  -- iexact H

/-- Tests introducing and extracting a pure hypothesis in affine BI -/
example [BI PROP] [BIAffine PROP] φ (Q : PROP) : ⊢ ⌜φ⌝ -∗ Q -∗ Q := by
  iaesop?
  -- iintro %Hφ HQ
  -- iexact HQ

/-- Tests introducing with disjunction pattern inside intuitionistic -/
example [BI PROP] (P1 P2 Q : PROP) : □ (P1 ∨ P2) ∗ Q ⊢ Q := by
  iintro ⟨#(_HP1 | _HP2), HQ⟩
  <;> iexact HQ

/-- Tests introducing multiple spatial hypotheses -/
example [BI PROP] (P Q : PROP) : ⊢ <affine> P -∗ Q -∗ Q := by
  iaesop?


/-- Tests introducing multiple intuitionistic hypotheses -/
example [BI PROP] (Q : PROP) : ⊢ □ P -∗ □ Q -∗ Q := by
  iaesop?
  -- iintro #_HP #HQ
  -- iexact HQ

/-- Tests introducing with complex nested patterns -/
example [BI PROP] (Q : PROP) : ⊢ □ (P1 ∧ P2) -∗ Q ∨ Q -∗ Q := by
  iaesop?
  -- iintro #⟨_HP1, ∗_HP2⟩ (HQ | HQ)
  -- <;> iexact HQ

end intro

end normalization.intro
