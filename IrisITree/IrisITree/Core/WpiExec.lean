module

public import IrisITree.Core.Exec

@[expose] public section

namespace IrisITree.Core

open Iris BI ITree Std OFE

/-- The constant-Φ weakest precondition functional.
    Unlike `wpiF`, the postcondition Φ is fixed rather than varying. -/
def wpi_constF {E : Effect} {R : Type _} {PROP : Type _} [BI PROP] [BIFUpdate PROP]
    (H : IHandler PROP E) (Φ : R → PROP)
    (wpi : LeibnizO (ITree E R) → PROP) :
    LeibnizO (ITree E R) → PROP :=
  λ t => iprop(
    |={∅}=> match t.car.unfold with
    | ITreeF.ret r => Φ r
    | ITreeF.tau t' => wpi ⟨t'⟩
    | ITreeF.vis i k => H.ihandle i
        (λ a => wpi ⟨k a⟩)
        (λ a => iprop(|={⊤,∅}=> wpi ⟨k a⟩))
  )

section wp_itree_const

variable {E : Effect} {R : Type _} {PROP : Type _} [BI PROP] [BIFUpdate PROP]

instance wpi_constF_ne (H : IHandler PROP E) (Φ : R → PROP) :
    NonExpansive (wpi_constF H Φ) where
  ne {_ wp1 wp2} Hwp := by
    intro t
    cases h : t.car.unfold <;> simp [wpi_constF, h]
    case tau t' => exact BIFUpdate.ne.ne <| Hwp ⟨t'⟩
    case vis i k =>
      apply BIFUpdate.ne.ne
      apply OFE.NonExpansive₂.ne (f := H.ihandle i)
      · intro a; apply Hwp ⟨k a⟩
      · intro a; apply BIFUpdate.ne.ne <| Hwp ⟨k a⟩

theorem wpi_constF_mono (H : IHandler PROP E) (Φ : R → PROP)
    (wp1 wp2 : LeibnizO (ITree E R) → PROP) :
    ⊢ □ (∀ t, wp1 t -∗ wp2 t) -∗
      ∀ t, wpi_constF H Φ wp1 t -∗ wpi_constF H Φ wp2 t := by
  iintro #Hwand %t Hwp; unfold wpi_constF
  cases t.car.unfold <;> simp
  case ret => iexact Hwp
  case tau t' => imod Hwp; imodintro; iapply Hwand $$ Hwp
  case vis i k =>
    imod Hwp; imodintro; iapply H.ihandle_mono
    · iintro %a Hk; iapply Hwand $$ Hk
    · iintro !> %a Hk; imod Hk; imodintro; iapply Hwand $$ Hk
    · iexact Hwp

instance wp_itree_const_mono (H : IHandler PROP E) (Φ : R → PROP) :
    BIMonoPred (wpi_constF H Φ) where
  mono_pred := by
    iintro %wp1 %wp2 %Hne1 %Hne2 #Hwand %t Hwp
    iapply wpi_constF_mono H Φ wp1 wp2 $$ [] Hwp
    iexact Hwand
  mono_pred_ne.ne n t1 t2 Hdist := by
    cases Hdist; rfl

/-- The constant-Φ weakest precondition, as the least fixpoint of `wpi_constF`. -/
def wpi_const (H : IHandler PROP E) (Φ : R → PROP) : ITree E R → PROP :=
  λ t => bi_least_fixpoint (wpi_constF H Φ) ⟨t⟩

theorem wpi_const_iter (H : IHandler PROP E) (Φ : R → PROP)
    (P : LeibnizO (ITree E R) → PROP) [NonExpansive P] :
    ⊢ □ (∀ y, wpi_constF H Φ P y -∗ P y) -∗
      ∀ t, bi_least_fixpoint (wpi_constF H Φ) t -∗ P t :=
  @least_fixpoint_iter _ _ _ _ (wpi_constF H Φ) P _

end wp_itree_const

/-- The thread-pool weakest precondition, built from `wpi_constF` and `lfp_tp`. -/
def wpi_tp {E : Effect} {R : Type _} {PROP : Type _} [BI PROP] [BIFUpdate PROP]
    (H : IHandler PROP E)
    (Ms : List (((LeibnizO (ITree E R) → PROP) → PROP)))
    (Φ : R → PROP) : PROP :=
  lfp_tp (wpi_constF H Φ) Ms

macro:20 "WPi_tp " ts:term:20 " @ " H:term:20 " {{ " Φ:term:20 " }}" : term => `(wpi_tp $H $ts $Φ)
macro:20 "WPi_tp " ts:term:20 " @ " H:term:20 " {{ " v:ident " , " Q:term:20 " }}" : term => `(wpi_tp $H $ts (fun $v => $Q))

section wpi_tp_section

variable {E : Effect} {R : Type _} {PROP : Type _} [BI PROP] [BIFUpdate PROP] [BIAffine PROP]

theorem wpi_tp_intro (t : ITree E R) (H : IHandler PROP E) (Φ : R → PROP) :
    (WPi t @> H {{ Φ }}) ⊢ wpi_tp H [λ P => P ⟨t⟩] Φ := by
  sorry

theorem wpi_tp_perm (H : IHandler PROP E) (Φ : R → PROP)
    (Ms1 Ms2 : List (((LeibnizO (ITree E R) → PROP) → PROP)))
    (h : Ms1.Perm Ms2) :
    wpi_tp H Ms1 Φ ⊣⊢ wpi_tp H Ms2 Φ := by
  simp only [wpi_tp]
  isplit <;> iintro Htp
  · iapply lfp_tp_perm (wpi_constF H Φ) Ms1 Ms2 h $$ Htp
  · iapply lfp_tp_perm (wpi_constF H Φ) Ms2 Ms1 h.symm $$ Htp

end wpi_tp_section

end IrisITree.Core
