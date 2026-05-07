module

public import Iris.BI
public import Iris.ProofMode

@[expose] public section

namespace Iris.Tests
open Iris.BI

namespace normalization.intro

-- namespace intro

-- /-- Tests introducing a spatial hypothesis -/
-- example [BI PROP] (Q : PROP) : Q ⊢ Q := by
--   iaesop
--   -- iintro HQ
--   -- iexact HQ

-- /-- Tests introducing an intuitionistic hypothesis with the `#` pattern -/
-- example [BI PROP] (Q : PROP) : □ Q ⊢ Q := by
--   iaesop
--   -- iintro #HQ
--   -- iexact HQ

-- /-- Tests introducing an affine persistent proposition as intuitionistic -/
-- example [BI PROP] (Q : PROP) : <affine> <pers> Q ⊢ Q := by
--   iaesop
--   -- iintro #HQ
--   -- iexact HQ

-- /-- Tests introducing a persistent implication in the spatial context -/
-- example [BI PROP] (Q : PROP) : ⊢ <pers> Q → Q := by
--   iaesop
--   -- iintro h
--   -- icases h with#h_1
--   -- iassumption

-- /- Tests introducing an implication in an intuitionistic context -/
-- example [BI PROP] (P : PROP) : ⊢ □ P -∗ P → P := by
--   iaesop
--   -- iintro h
--   -- iintro h_1
--   -- icases h with#h_2
--   -- iassumption

-- /-- Tests dropping a hypothesis in an implication with the `-` pattern -/
-- example [BI PROP] (Q : PROP) : ⊢ P → Q -∗ Q := by
--   iaesop
--   -- iintro h
--   -- iintro h_1
--   -- iassumption

-- /-- Tests dropping a hypothesis in an implication in a non-empty context -/
-- example [BI PROP] (Q : PROP) : ⊢ Q -∗ P → Q := by
--   iaesop
--   -- iintro h
--   -- iintro-
--   -- simp_all only [Std.refl]

-- /-- Tests introducing an universally quantified variable -/
-- example [BI PROP] : ⊢@{PROP} ∀ x, ⌜x = 0⌝ → ⌜x = 0⌝ := by
--   iaesop
--   -- iintro%x
--   -- iintro%x_1
--   -- subst x_1
--   -- simp_all only
--   -- ipure_intro
--   -- simp_all only

-- /-- Tests introducing and extracting a pure hypothesis in affine BI -/
-- example [BI PROP] [BIAffine PROP] φ (Q : PROP) : ⊢ ⌜φ⌝ -∗ Q -∗ Q := by
--   iaesop
--   -- iintro%x
--   -- iintro h
--   -- simp_all only [Std.refl]

-- /-- Tests introducing with disjunction pattern inside intuitionistic -/
-- example [BI PROP] (P1 P2 Q : PROP) : □ (P1 ∨ P2) ∗ Q ⊢ Q := by
--   iaesop
--   -- iintro h
--   -- icases h with⟨h1, h2⟩
--   -- icases h1 with#h
--   -- iassumption

-- /-- Tests introducing multiple spatial hypotheses -/
-- example [BI PROP] (P Q : PROP) : ⊢ <affine> P -∗ Q -∗ Q := by
--   iaesop
--   -- iintro h
--   -- iintro h_1
--   -- iassumption

-- /-- Tests introducing multiple intuitionistic hypotheses -/
-- example [BI PROP] (Q : PROP) : ⊢ □ P -∗ □ Q -∗ Q := by
--   iaesop
--   -- iintro h
--   -- iintro h_1
--   -- icases h with#h_2
--   -- icases h_1 with#h
--   -- iassumption

-- /-- Tests introducing with complex nested patterns -/
-- example [BI PROP] (Q : PROP) : ⊢ □ (P1 ∧ P2) -∗ Q ∨ Q -∗ Q := by
--   iaesop
--   -- iintro h
--   -- iintro h_1
--   -- icases h with#h_2
--   -- icases h_2 with⟨h1, h2⟩
--   -- icases h_1 with(h1_1 | h2_1)
--   -- · iassumption
--   -- · iassumption

-- end intro

-- namespace pure

-- example [BI PROP] (Q : PROP) : <affine> ⌜φ⌝ ⊢ Q -∗ Q := by
--   iaesop
--   -- iintro%x
--   -- iintro h
--   -- simp_all only [Std.refl]

-- /-- Tests `ipure` with multiple pure hypotheses -/
-- example [BI PROP] (Q : PROP) : <affine> ⌜φ1⌝ ⊢ <affine> ⌜φ2⌝ -∗ Q -∗ Q := by
--   iaesop
--   -- iintro%x
--   -- iintro%x_1
--   -- iintro h
--   -- simp_all only [Std.refl]

-- /-- Tests `ipure` with conjunction containing pure -/
-- example [BI PROP] (Q : PROP) : (⌜φ1⌝ ∧ <affine> ⌜φ2⌝) ⊢ Q -∗ Q := by
--   iaesop
--   -- iintro%x
--   -- iintro h
--   -- simp_all only [Std.refl]

-- end pure


-- namespace cases

-- /-- Tests `icases` with nested conjunction -/
-- example [BI PROP] (Q : PROP) : □ (P1 ∧ P2 ∧ Q) ⊢ Q := by
--   iaesop
--   -- iintro h
--   -- icases h with#h_1
--   -- icases h_1 with⟨h1, h2⟩
--   -- icases h2 with⟨h1_1, h2_1⟩
--   -- iassumption

-- /-- Tests `icases` with intuitionistic conjunction -/
-- example [BI PROP] (Q : PROP) : □ P ∧ Q ⊢ Q := by
--   iaesop
--   -- iintro h
--   -- iassumption

-- /-- Tests `icases` on conjunction with persistent left -/
-- example [BI PROP] (Q : PROP) : <pers> Q ∧ <affine> P ⊢ Q := by
--   iaesop
--   -- iintro h
--   -- icases h with⟨h1, h2⟩
--   -- icases h1 with#h
--   -- iassumption

-- /-- Tests `icases` on conjunction with persistent right -/
-- example [BI PROP] (Q : PROP) : Q ∧ <pers> P ⊢ Q := by
--   iaesop
--   -- iintro h
--   -- icases h with⟨h1, h2⟩
--   -- icases h2 with#h
--   -- iassumption

-- /-- Tests `icases` with nested separating conjunction -/
-- example [BI PROP] [BIAffine PROP] (Q : PROP) : P1 ∗ P2 ∗ Q ⊢ Q := by
--   iaesop
--   -- iintro h
--   -- icases h with⟨h1, h2⟩
--   -- icases h2 with⟨h1_1, h2_1⟩
--   -- iassumption

-- /-- Tests `icases` with nested disjunction -/
-- example [BI PROP] (Q : PROP) : ⊢ <affine> (Q ∨ Q ∨ Q) -∗ Q := by
--   iaesop
--   -- iintro h
--   -- icases h with(h1 | h2)
--   -- · iassumption
--   -- · icases h2 with(h1 | h2_1)
--   --   · iassumption
--   --   · iassumption

-- /-- Tests `icases` with complex mixed conjunction and disjunction -/
-- example {PROP P11 P12 P13 P2 P31 P32 P33} [BI PROP] [BIAffine PROP] (Q : PROP) :
--     (P11 ∨ P12 ∨ P13) ∗ P2 ∗ (P31 ∨ P32 ∨ P33) ∗ Q ⊢ Q := by
--   iaesop
--   -- iintro h
--   -- icases h with⟨h1, h2⟩
--   -- icases h2 with⟨h1_1, h2_1⟩
--   -- icases h2_1 with⟨h1_2, h2⟩
--   -- iassumption

-- /-- Tests `icases` moving pure to Lean context with % -/
-- example [BI PROP] (Q : PROP) : ⊢ <affine> ⌜⊢ Q⌝ -∗ Q := by
--   iaesop
--   -- iintro%x
--   -- exact x

-- /-- Tests `icases` moving pure to Lean context with % -/
-- example [BI PROP] (Q : PROP) : ⊢ <affine> ⌜⊢ Q⌝ -∗ Q := by
--   iaesop
--   -- iintro%x
--   -- exact x

-- /-- Tests `icases` moving to intuitionistic with # -/
-- example [BI PROP] (Q : PROP) : ⊢ □ Q -∗ Q := by
--   iaesop
--   -- iintro h
--   -- icases h with#h_1
--   -- iassumption

-- /-- Tests `icases` moving to intuitionistic with # -/
-- example [BI PROP] (Q : PROP) : ⊢ □ Q -∗ Q := by
--   iaesop
--   -- iintro h
--   -- icases h with#h_1
--   -- iassumption

-- /-- Tests `icases` with pure in conjunction -/
-- example [BI PROP] (Q : PROP) : ⊢ <affine> ⌜φ⌝ ∗ Q -∗ Q := by
--   iaesop
--   -- iintro h
--   -- icases h with⟨h1, h2⟩
--   -- icases h1 with%x
--   -- simp_all only [Std.refl]

-- /-- Tests `icases` with pure in disjunction -/
-- example [BI PROP] (Q : PROP) :
--     ⊢ <affine> ⌜φ1⌝ ∨ <affine> ⌜φ2⌝ -∗ Q -∗ Q := by
--   iintro#h
--   iintro h_1
--   icases h with%x
--   iexact h_1
--   -- iintro%x
--   -- iintro h
--   -- simp_all only [Std.refl]

-- /-- Tests `icases` with intuitionistic in conjunction -/
-- example [BI PROP] (Q : PROP) : ⊢ □ P ∗ Q -∗ Q := by
--   iaesop
--   -- iintro h
--   -- icases h with⟨h1, h2⟩
--   -- icases h1 with#h
--   -- iassumption

-- /-- Tests `icases` with intuitionistic in disjunction -/
-- example [BI PROP] (Q : PROP) : ⊢ □ Q ∨ Q -∗ Q := by
--   iaesop?
--   -- iintro h
--   -- icases h with(h1 | h2)
--   -- · icases h1 with#h
--   --   iassumption
--   -- · simp_all only [Std.refl]

-- /-- Tests `icases` moving to spatial inside intuitionistic conjunction -/
-- example [BI PROP] (Q : PROP) : ⊢ □ (P ∧ Q) -∗ Q := by
--   iaesop?
--   -- iintro h
--   -- icases h with#h_1
--   -- icases h_1 with⟨h1, h2⟩
--   -- iassumption

-- /-- Tests `icases` destructing multiple conjunctions  -/
-- example [BI PROP] (Q : PROP) : P1 ∧ P2 ∧ Q ∧ P3 ⊢ Q := by
--   iaesop
--   -- iintro h
--   -- iassumption

-- /-- Tests `icases` destructing multiple intuitionistic conjunctions -/
-- example [BI PROP] (Q : PROP) : □ (P1 ∧ P2 ∧ Q ∧ P3) ⊢ Q := by
--   iaesop
--   -- iintro h
--   -- icases h with#h_1
--   -- icases h_1 with⟨h1, h2⟩
--   -- icases h2 with⟨h1_1, h2_1⟩
--   -- icases h2_1 with⟨h1_2, h2⟩
--   -- iassumption

-- /-- Tests `icases` with existential -/
-- example [BI PROP] (Q : Nat → PROP) : (∃ x, Q x) ⊢ ∃ x, Q x ∨ False := by
--   iaesop?
--   iexists x
--   iaesop
--   -- ileft
--   -- simp_all only [Std.refl]

-- /-- Tests `icases` with intuitionistic existential -/
-- example [BI PROP] (Q : Nat → PROP) : □ (∃ x, Q x) ⊢ ∃ x, □ Q x ∨ False := by
--   iaesop
--   iexists x
--   iaesop
--   -- ileft
--   -- simp_all only [Std.refl]

-- /-- Tests `icases` with proof mode term -/
-- example [BI PROP] P (Q : Nat → PROP) :
--   (P -∗ ∃ x, □ Q x ∗ Q 1) ⊢ P -∗ Q 1 := by
--   iintro Hwand HP
--   icases Hwand $$ HP with ⟨%_, -, HQ⟩
--   iexact HQ

-- /-- Tests `icases` with a comprehensive nested pattern combining existential, pure,
-- intuitionistic, spatial, disjunction, and clearing. -/
-- example [BI PROP] (φ : Prop) (Q : PROP) :
--     □ (∃ _ : Nat, ⌜φ⌝ ∧ Q) ∗ (Q ∨ False) ⊢ Q := by
--   iaesop
--   -- iintro h
--   -- icases h with⟨h1, h2⟩
--   -- icases h1 with#h
--   -- icases h2 with(h1 | h2_1)
--   -- · iassumption
--   -- · icases h2_1 with%x
--   --   simp_all only

-- /-- Tests `icases` with multiple mod patterns -/
-- example [BI PROP] [BIUpdate PROP] (P Q : PROP) : (|==> P) ∗ (|==> Q) ⊢ |==> (P ∗ Q) := by
--   iaesop
--   -- iintro h
--   -- icases h with⟨h1, h2⟩
--   -- imod h1
--   -- imod h2
--   -- imodintro
--   -- simp_all only [Std.refl]

-- /- Tests `icases` with a comprehensive nested fancy-update pattern combining mask changes,
-- existential, pure, disjunction, conjunction, clearing, and multiple mod eliminations. -/
-- set_option Elab.async false in
-- #time
-- example [BI PROP] [BIUpdate PROP] [BIFUpdate PROP] [BIUpdateFUpdate PROP]
--     (E1 E2 E3 : CoPset) (φ : Prop) (P Q : PROP) :
--     (|={E1,E2}=> ∃ _ : Nat, ⌜φ⌝ ∧ P) ∗
--       ((|={E2,E3}=> <affine> Q ∗ emp) ∨ (|={E2,E3}=> emp ∗ <affine> Q)) ⊢
--       |={E1,E3}=> P := by
--   iaesop
--   -- iintro h
--   -- icases h with⟨h1, h2⟩
--   -- icases h2 with(h1_1 | h2_1)
--   -- · imod h1
--   --   icases h1 with⟨%x, h⟩
--   --   imod h1_1
--   --   icases h1_1 with⟨h1, h2⟩
--   --   icases h2 with#h_1
--   --   icases h with⟨h1_1, h2⟩
--   --   icases h1_1 with%x_1
--   --   iassumption
--   -- · imod h1
--   --   icases h1 with⟨%x, h⟩
--   --   imod h2_1
--   --   icases h2_1 with⟨h1, h2⟩
--   --   icases h1 with#h_1
--   --   icases h with⟨h1, h2_1⟩
--   --   icases h1 with%x_1
--   --   iassumption

-- /-- Tests `icases` duplicating the context -/
-- example [BI PROP] (Q : PROP) (n : Nat) :
--     □ (∀ x, Q -∗ ⌜x = n⌝) ⊢ Q -∗ False := by
--   iintro #Hwand HQ
--   icases Hwand $$ %1 HQ with %_
--   icases Hwand $$ %2 HQ with %_
--   grind

-- /-- Tests `icases` removing a destructed hyp -/
-- example [BI PROP] [BIAffine PROP] (Q : PROP) :
--     □ (Q ∗ Q) ⊢ □ Q ∗ □ Q := by
--   iaesop
--   -- iintro h
--   -- icases h with#h_1
--   -- icases h_1 with⟨h1, h2⟩
--   -- simp_all only [Std.refl]


-- /-- Tests `icases` with False -/
-- example [BI PROP] (Q : PROP) : False ⊢ Q := by
--   iaesop
--   -- iintro%x
--   -- simp_all only

-- end cases


-- -- apply
-- namespace apply

-- /-- Tests `iapply` with wand -/
-- example [BI PROP] (P Q : PROP) : ⊢ P -∗ (P -∗ Q) -∗ Q := by
--   iaesop
--   -- iintro HP H
--   -- iapply H $$ HP

-- /-- Tests `iapply` with multiple hypotheses -/
-- example [BI PROP] (P Q R : PROP) : ⊢ P -∗ Q -∗ (P -∗ Q -∗ R) -∗ R := by
--   iaesop
--   -- iintro HP HQ H
--   -- iapply H $$ HP HQ

-- /-- Tests `iapply` with nested wand application -/
-- example [BI PROP] (P Q R S : PROP) : ⊢ (P -∗ Q) -∗ P -∗ R -∗ (Q -∗ R -∗ S) -∗ S := by
--   iaesop
--   -- iintro HPQ HP HR H
--   -- iapply H $$ [HPQ HP] HR
--   -- iapply HPQ $$ HP

-- /-- Tests `iapply` with intuitionistic wand argument -/
-- example [BI PROP] (P Q : PROP) : ⊢ □ P -∗ (P -∗ Q) -∗ Q := by
--   iaesop
--   -- iintro HP H
--   -- iapply H $$ HP

-- /-- Tests `iapply` with multiple intuitionistic hypotheses and subgoals -/
-- example [BI PROP] (P Q R : PROP) : ⊢ □ P -∗ Q -∗ □ (P -∗ Q -∗ □ R) -∗ R := by
--   iaesop
--   -- iintro h
--   -- iintro h_1
--   -- iintro h_2
--   -- icases h with#h_3
--   -- icases h_2 with#h
--   -- iapply h$$h_3 h_1

-- /-- Tests `iapply` with later modality -/
-- example [BI PROP] (P Q : PROP) : ⊢ (▷ P -∗ Q) -∗ P -∗ Q := by
--   iaesop
--   -- iintro H HP
--   -- iapply H $$ HP

-- /-- Tests `iapply` with implication -/
-- example [BI PROP] [BIAffine PROP] (P Q : PROP) : ⊢ (P → Q) -∗ <pers> P -∗ Q := by
--   iaesop

-- /-- Tests `iapply` with later and implication -/
-- example [BI PROP] [BIAffine PROP] (P Q : PROP) : ⊢ (▷ P → Q) -∗ P -∗ Q := by
--   iaesop
--   -- iintro H HP
--   -- iapply H $$ HP

-- /-- Tests `iapply` with lemma -/
-- example [BI PROP] (Q : PROP) : Q ⊢ (emp ∗ Q) ∗ emp := by
--   -- iaesop
--   iapply (wand_intro sep_emp.mpr)
--   iemp_intro

-- /-- Tests `iapply` with pure sidecondition -/
-- example [BI PROP] (Q : PROP) (H : 0 = 0 → ⊢ Q) : ⊢ Q := by
--   iaesop

-- /-- Tests `iapply` with lemma with sidecondition -/
-- example [BI PROP] : ⊢@{PROP} ⌜1 = 1⌝ := by
--   istart
--   iapply (pure_intro (P:=emp))
--   . rfl
--   iemp_intro

-- /-- Tests `iapply` with entailment as Lean hypothesis -/
-- example [BI PROP] (P Q : PROP) (H : P ⊢ Q) (HP : ⊢ P) : ⊢ Q := by
--   iaesop

-- /-- Tests `iapply` with wand entailment as Lean hypothesis -/
-- example [BI PROP] (P Q : PROP) (H : ⊢ P -∗ Q) (HP : ⊢ P) : ⊢ Q := by
--   iaesop

-- /-- Tests `iapply` with constructed term -/
-- example [BI PROP] (P Q : PROP) (H1 : P ⊢ Q) (H2 : Q ⊢ R) : P ⊢ R := by
--   iintro HP
--   iapply (wand_intro (emp_sep.mp.trans H2))
--   . ipure_intro; trivial
--   iapply H1 $$ HP

-- /-- Tests `iapply` with Lean wand entailment and subgoal -/
-- example [BI PROP] (P Q R : PROP) (H : P ⊢ Q -∗ R) (HP : ⊢ P) : ⊢ Q -∗ R := by
--   iintro HQ
--   iapply H $$ [] HQ
--   iapply HP

-- /-- Tests `iapply` with lemma and subgoal -/
-- example [BI PROP] (P Q R : PROP) (H : P ∗ Q ⊢ R) (HP : ⊢ P) : ⊢ Q -∗ R := by
--   iintro HQ
--   iapply (wand_intro H) $$ [] HQ
--   iapply HP

-- /-- Tests `iapply` with forall -/
-- example [BI PROP] (P : α → PROP) (a : α) (H : ⊢ ∀ x, P x) : ⊢ P a := by
--   istart
--   iapply H

-- /-- Tests `iapply` with Lean forall -/
-- example [BI PROP] (P : α → PROP) (a : α) (H : ∀ x, ⊢ P x) : ⊢ P a := by
--   iaesop

-- /-- Tests `iapply` with forall specialization -/
-- example [BI PROP] (P Q : α → PROP) (a b : α) (H : ⊢ ∀ x, ∀ y, P x -∗ Q y) : P a ⊢ Q b := by
--   iintro HP
--   iapply H $$ %a %b HP

-- /-- Tests `iapply` with forall specialization from hypothesis -/
-- example [BI PROP] (P Q : α → PROP) (a b : α) : (∀ x, ∀ y, P x -∗ Q y) ⊢ P a -∗ Q b := by
--   iintro H HP
--   iapply H $$ %a %b HP

-- /-- Tests `iapply` with tactic -/
-- example [BI PROP] (P Q : α → PROP) (a b : α) : (∀ x, ∀ y, P x -∗ Q y) ⊢ P a -∗ Q b := by
--   iintro H HP
--   iapply H $$ %(by exact a) %b [HP]
--   iapply HP

-- /-- Tests `iapply` with pure hypothesis -/
-- example [BI PROP] (Q : α → PROP) (a b : α) : (∀ x, ∀ y, ⌜x = a⌝ -∗ Q y) ⊢ Q b := by
--   iintro H
--   iapply H $$ %_ %b %rfl

-- /-- error: ispecialize: iprop(P a -∗ Q b) is not a lean premise -/
-- #guard_msgs in
-- example [BI PROP] (P Q : α → PROP) (a b : α) : (∀ x, ∀ y, P x -∗ Q y) ⊢ P a -∗ Q b := by
--   iintro H HP
--   iapply H $$ %a %b %_ HP

-- /-- Tests `iapply` using unification for foralls -/
-- example [BI PROP] (P Q : α → PROP) (a b : α) : (∀ x, ∀ y, P x -∗ Q y) ⊢ P a -∗ Q b := by
--   iintro H HP
--   iapply H $$ HP

-- /-- Tests `iapply` using manually created metavariables -/
-- example [BI PROP] (P Q : α → PROP) (a b : α) : (∀ x, ∀ y, P x -∗ Q y) ⊢ P a -∗ Q b := by
--   iintro H HP
--   iapply H $$ %?_ %?_ HP

-- /-- Tests `iapply` using unification in two steps, instantiating metavars  -/
-- example [BI PROP] (P Q : α → PROP) (a b : α) : (∀ x, ∀ y, P x -∗ Q y) ⊢ P a -∗ Q b := by
--   iintro H HP
--   iapply H
--   iapply HP

-- /-- Tests `iapply` with intuitionistic forall from Lean -/
-- example [BI PROP] (P Q : α → PROP) (a b : α) (H : ⊢ □ ∀ x, ∀ y, P x -∗ Q y) : P a ⊢ Q b := by
--   iintro HP
--   iapply H $$ %a HP

-- /-- Tests `iapply` with intuitionistic forall from hypothesis -/
-- example [BI PROP] (P Q : α → PROP) (a b : α) : (□ ∀ x, ∀ y, P x -∗ Q y) ⊢ P a -∗ Q b := by
--   iaesop
--   -- iintro h
--   -- iintro h_1
--   -- icases h with#h_2
--   -- iapply h_2$$h_1

-- /-- Tests `iapply` with two wands and subgoals -/
-- example [BI PROP] (P Q : Nat → PROP) :
--   (P 1 -∗ P 2 -∗ Q 1) ⊢ □ P 1 -∗ P 2 -∗ Q 1 := by
--   iintro H #HP1 HP2
--   iapply H
--   . iexact HP1
--   . iexact HP2

-- /-- Tests `iapply` selecting left conjunct -/
-- example [BI PROP] (P Q : Nat → PROP) :
--   ((P 1 -∗ P 2) ∧ (Q 1 -∗ Q 2)) ⊢ P 1 -∗ P 2 := by
--   iintro H HP1
--   iapply H
--   iexact HP1

-- /-- Tests `iapply` selecting right conjunct -/
-- example [BI PROP] (P Q : Nat → PROP) :
--   ((P 1 -∗ P 2) ∧ (Q 1 -∗ Q 2)) ⊢ Q 1 -∗ Q 2 := by
--   iintro H HQ1
--   iapply H
--   iexact HQ1

-- /-- Tests `iapply` selecting left conjunct (exact match) -/
-- example [BI PROP] (P Q : Nat → PROP) :
--   (P 1 ∧ Q 1) ⊢ P 1 := by
--   iintro H
--   iapply H

-- /-- Tests `iapply` selecting right conjunct (exact match) -/
-- example [BI PROP] (P Q : Nat → PROP) :
--   (P 1 ∧ Q 1) ⊢ Q 1 := by
--   iintro H
--   iapply H

-- /-- Tests delayed split planning with exact-only footprints -/
-- example [BI PROP] (P Q : PROP) : P ∗ Q ⊢ Q ∗ P := by
--   iaesop?

-- /- Tests `iapply` exact matching, but not affine -/
-- /-- error: iapply: the context P is not affine and goal not absorbing -/
-- #guard_msgs in
-- example [BI PROP] (P Q : PROP) : Q ⊢ P -∗ Q := by
--   iintro H HP
--   iapply H

-- -- TODO: real annoying stuff
-- example [BI PROP] (P Q R₁ R₂ : PROP) :
--     ⊢ P -∗ Q -∗ (P -∗ R₁) -∗ (P -∗ Q -∗ R₁)
--     -∗ (Q -∗ R₂) -∗ (Q -∗ P -∗ R₂) -∗ (R₁ ∗ R₂) := by
--   iaesop
--   sorry

-- end apply


end normalization.intro
