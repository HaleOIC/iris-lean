module

public import IrisITree.Core.ITree
public import IrisITree.Core.Exec

@[expose] public section

namespace IrisITree.Core

open Iris BI ITree Std

/-- The constant-Φ weakest precondition functional.
    Unlike `wpiF`, the postcondition Φ is fixed rather than varying. -/
def wpiConstF {E : Effect} {R : Type _} {PROP : Type _} [BI PROP] [BIFUpdate PROP]
    (H : IHandler PROP E) (Φ : R → PROP)
    (wpi : ITree E R → PROP) :
    ITree E R → PROP :=
  λ t => iprop(|={∅}=>
      match t.unfold with
      | ITreeF.ret r => Φ r
      | ITreeF.tau t' => wpi t'
      | ITreeF.vis i k => H.ihandle i (λ a => wpi (k a)) (λ a => wpi (k a)))

section wp_itree_const

variable {E : Effect} {R : Type _} {PROP : Type _} [BI PROP] [BIFUpdate PROP]

instance (H : IHandler PROP E) (Φ : R → PROP) :
    OFE.NonExpansive (wpiConstF H Φ) where
  ne {_ wp1 wp2} Hwp := by
    intro t
    cases t <;> simp [wpiConstF]
    case tau t' => exact BIFUpdate.ne.ne <| Hwp t'
    case vis i k =>
      apply BIFUpdate.ne.ne
      apply OFE.NonExpansive₂.ne (f := H.ihandle i)
      · intro a; apply Hwp (k a)
      · intro a; apply Hwp (k a)

theorem wpiConstF_mono (H : IHandler PROP E) (Φ : R → PROP)
    (wp1 wp2 : ITree E R → PROP) :
    □ (∀ t, wp1 t -∗ wp2 t) -∗
    ∀ t, wpiConstF H Φ wp1 t -∗ wpiConstF H Φ wp2 t := by
  iintro #Hwand %t Hwp
  cases t <;> simp [wpiConstF]
  case ret => iframe
  case tau t' => imod Hwp; imodintro; iapply Hwand $$ Hwp
  case vis i k =>
    imod Hwp; imodintro; iapply H.ihandle_mono $$ [] [] Hwp
    · iintro %a Hk; iapply Hwand $$ Hk
    · iintro !> %a Hk; iapply Hwand $$ Hk

instance wp_itree_const_mono (H : IHandler PROP E) (Φ : R → PROP) :
    BIMonoPred (wpiConstF H Φ) where
  mono_pred := by
    iintro %wp1 %wp2 %Hne1 %Hne2 #Hwand %t Hwp
    iapply wpiConstF_mono $$ Hwand Hwp
  mono_pred_ne.ne n t1 t2 Hdist := by
    cases Hdist; rfl

/-- The constant-Φ weakest precondition, as the least fixpoint of `wpi_constF`. -/
def wpiConst (H : IHandler PROP E) (Φ : R → PROP) : ITree E R → PROP :=
  bi_least_fixpoint (wpiConstF H Φ)

theorem wpi_const_iter (H : IHandler PROP E) (Φ : R → PROP)
    (P : ITree E R → PROP)  :
    □ (∀ y, wpiConstF H Φ P y -∗ P y) -∗
    ∀ t, wpiConst H Φ t -∗ P t :=
  have : OFE.NonExpansive P := by constructor; rintro _ _ _ ⟨_⟩; exact .rfl
  @least_fixpoint_iter _ _ _ _ (wpiConstF H Φ) P _

end wp_itree_const

/-- The thread-pool weakest precondition, built from `wpiConstF` and `lfp_tp`. -/
def wpi_tp {E : Effect} {R : Type _} {PROP : Type _} [BI PROP] [BIFUpdate PROP]
    (H : IHandler PROP E)
    (Ms : List (((ITree E R → PROP) → PROP)))
    (Φ : R → PROP) : PROP :=
  lfp_tp (wpiConstF H Φ) Ms

macro:20 "WPi_tp " ts:term:20 " @ " H:term:20 " {{ " Φ:term:20 " }}" : term => `(wpi_tp $H $ts $Φ)
macro:20 "WPi_tp " ts:term:20 " @ " H:term:20 " {{ " v:ident " , " Q:term:20 " }}" : term => `(wpi_tp $H $ts (fun $v => $Q))

section wpi_tp_section

variable {E : Effect} {R : Type _} {PROP : Type _} [BI PROP] [BIFUpdate PROP] [BIAffine PROP]

theorem wpi_tp_intro (t : ITree E R) (H : IHandler PROP E) (Φ : R → PROP) :
    WPi t @> H; ∅ {{ Φ }} ⊢ wpi_tp H [λ P => P t] Φ := by
  sorry

theorem wpi_tp_perm (H : IHandler PROP E) (Φ : R → PROP)
    Ms1 Ms2
    (h : Ms1.Perm Ms2) :
    wpi_tp H Ms1 Φ ⊣⊢ wpi_tp H Ms2 Φ := by
  simp only [wpi_tp]
  isplit <;> iintro Htp
  · iapply lfp_tp_perm $$ Htp; assumption
  · have := h.symm
    iapply lfp_tp_perm $$ Htp; assumption

end wpi_tp_section

/-
section wpi_adequate

open ITree.Exec

variable {E : Effect.{u} } {R : Type u} {σ : Type _} [BIAffine PROP]

theorem wpi_adequate_ind (Φ : R → PROP) (H : IHandler PROP E)
    (EH : EHandler E E R σ) [A : EHandlerAdequate (PROP := PROP) H EH]
    (t : ITree E R) (s : σ)
    (Ms : List (((LeibnizO (ITree E R) → PROP) → PROP)))
    (Mss : List (((ITree E R → PROP) → PROP)))
    (M : (LeibnizO (ITree E R) → PROP) → PROP)
    (C : ITree E R → σ → Prop)
    (Hexec : exec EH t s C)
    (HMs : Ms.Perm (M :: Mss.map (λ M' P => M' (λ t => P ⟨t⟩)))) :
    ⊢ wpi_tp H Ms Φ -∗
      A.ehandler_inv s Mss -∗
      (∀ P, M P ={∅}=∗ P ⟨t⟩) -∗
      |={∅}=> ∃ t' s' Ms' M',
        ⌜C t' s'⌝ ∗
        A.ehandler_inv s' Ms' ∗
        bi_close Eq (λ t'' => iprop(∀ P, M' P ={∅}=∗ P t'')) ⟨t'⟩ ∗
        wpi_tp H (M' :: Ms'.map (λ M'' P => M'' (λ t => P ⟨t⟩))) Φ := by
  sorry

theorem wpi_adequate (Φ : R → PROP) (H : IHandler PROP E)
    (EH : EHandler E E R σ) [A : EHandlerAdequate (PROP := PROP) H EH]
    (t : ITree E R) (s : σ)
    (C : ITree E R → σ → Prop) (m : CoPset)
    (Hexec : exec EH t s C) :
    ⊢ iprop(|={m,∅}=> WPi t @> H {{v, iprop(|={∅,m}=> Φ v)}}) -∗
      A.ehandler_inv s [] -∗
      |={m, ∅}=> ∃ t' s' Ms' M',
      ⌜C t' s'⌝ ∗
      A.ehandler_inv s' Ms' ∗
      bi_close Eq (λ t'' => iprop(∀ P, M' P ={∅}=∗ P t'')) ⟨t'⟩ ∗
      wpi_tp H (M' :: Ms'.map (λ M'' P => M'' (λ t => P ⟨t⟩))) (λ v => iprop(|={∅,m}=> Φ v)) := by
  sorry

end wpi_adequate
-/

end IrisITree.Core
