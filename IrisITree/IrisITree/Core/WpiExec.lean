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

theorem wpiConstF_tau (H : IHandler PROP E) (Φ : R → PROP)
    (G : ITree E R → PROP) (t : ITree E R) :
    wpiConstF H Φ G t.tau ⊣⊢ iprop(|={∅}=> G t) := by
  simp [wpiConstF]

theorem wpiConstF_vis (H : IHandler PROP E) (Φ : R → PROP)
    (G : ITree E R → PROP) (i : E.I) (k : E.O i → ITree E R) :
    wpiConstF H Φ G (.vis i k) ⊣⊢
      iprop(|={∅}=> H.ihandle i (λ a => G (k a)) (λ a => G (k a))) := by
  simp [wpiConstF]

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

theorem wpi_wpiConst_step (t : ITree E R) (H : IHandler PROP E) (Φ Ψ : R → PROP) :
    ⊢ □ (∀ r, Ψ r -∗ Φ r) -∗
      wpiF H (λ Ms t Ψ => iprop(
        (□ (∀ r, Ψ r -∗ Φ r) -∗ bi_least_fixpoint (wpiConstF H Φ) t) ∧
        WPi t @> H; Ms, ∅ {{ Ψ }})) ∅ ∅ t Ψ -∗
      wpiConstF H Φ (bi_least_fixpoint (wpiConstF H Φ)) t := by
  iintro #Hpost
  cases t <;> simp [wpiConstF, wpiF]
  case ret r =>
    iintro Hstep; imod Hstep; imod Hstep; imodintro
    iapply Hpost $$ Hstep
  case tau t' =>
    iintro >Hstep; imodintro
    icases Hstep with ⟨Hconst, -⟩
    iapply Hconst $$ Hpost
  case vis i k =>
    iintro >Hstep; imodintro
    iapply H.ihandle_mono $$ [] [] Hstep
    · iintro %a Hk; icases Hk with ⟨Hconst, -⟩
      iapply Hconst $$ Hpost
    · iintro !> %a Hk; icases Hk with ⟨Hconst, -⟩
      iapply Hconst
      iintro !> %r Hfalse; icases Hfalse with ⟨⟩

theorem wpi_wpiConst_aux (t : ITree E R) (H : IHandler PROP E) (Φ Ψ : R → PROP) :
    WPi t @> H; ∅ {{ Ψ }} ⊢
      iprop(□ (∀ r, Ψ r -∗ Φ r) -∗ bi_least_fixpoint (wpiConstF H Φ) t) := by
  letI : ∀ t, OFE.NonExpansive (λ Ψ : R → PROP =>
      iprop(□ (∀ r, Ψ r -∗ Φ r) -∗ bi_least_fixpoint (wpiConstF H Φ) t)) :=
    fun _ => ⟨fun _ _ _ HΨ => wand_ne.ne
      (intuitionistically_ne.ne (forall_ne fun r => wand_ne.ne (HΨ r) .rfl)) .rfl⟩
  iintro Hwpi
  iapply (wpi_ind (Me := ∅) (λ t Ψ =>
    iprop(□ (∀ r, Ψ r -∗ Φ r) -∗ bi_least_fixpoint (wpiConstF H Φ) t))) $$ [] %t %Ψ Hwpi
  iintro !> %t %Ψ Hstep #Hpost
  ihave Hbody := wpi_wpiConst_step t H Φ Ψ $$ Hpost Hstep
  iapply least_fixpoint_unfold_mpr (F := wpiConstF H Φ) $$ Hbody

theorem wpi_wpiConst (t : ITree E R) (H : IHandler PROP E) (Φ : R → PROP) :
    WPi t @> H; ∅ {{ Φ }} ⊢ bi_least_fixpoint (wpiConstF H Φ) t := by
  iintro Hwpi
  iapply wpi_wpiConst_aux t H Φ Φ $$ Hwpi []
  iintro !> %r Hr; iexact Hr

theorem wpi_tp_intro (t : ITree E R) (H : IHandler PROP E) (Φ : R → PROP) :
    WPi t @> H; ∅ {{ Φ }} ⊢ wpi_tp H [λ P => P t] Φ := by
  iintro Hwpi
  unfold wpi_tp
  ihave Hconst := wpi_wpiConst t H Φ $$ Hwpi
  iapply lfp_tp_intro (wpiConstF H Φ) t $$ Hconst

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

section wpi_adequate

open ITree.Exec

variable {E : Effect.{u} } {R : Type u} {σ : Type _}
  [BI PROP] [BIFUpdate PROP] [BIAffine PROP]

theorem wpi_adequate_ind (Φ : R → PROP) (H : IHandler PROP E)
    (EH : EHandler E E R σ) [A : EHandlerAdequate (PROP := PROP) H EH]
    (t : ITree E R) (s : σ)
    (Ms Mss : List (((ITree E R → PROP) → PROP)))
    (M : (ITree E R → PROP) → PROP)
    (C : ITree E R → σ → Prop)
    (Hexec : exec EH t s C)
    (HMs : Ms.Perm (M :: Mss)) :
    ⊢ wpi_tp H Ms Φ -∗
      A.inv s Mss -∗
      (∀ P, M P ={∅}=∗ P t) -∗
      |={∅}=> ∃ t' s' Ms' M',
        ⌜C t' s'⌝ ∗
        A.inv s' Ms' ∗
        bi_close Eq (λ t'' => iprop(∀ P, M' P ={∅}=∗ P t'')) t' ∗
        wpi_tp H (M' :: Ms') Φ := by
  unfold wpi_tp
  letI : OFE.NonExpansive (λ Ms : DiscreteO (List ((ITree E R → PROP) → PROP)) =>
      iprop(∀ (t : ITree E R) (s : σ) (M : (ITree E R → PROP) → PROP)
        (Mss : List ((ITree E R → PROP) → PROP)) (C : ITree E R → σ → Prop),
        ⌜exec EH t s C⌝ -∗ ⌜Ms.car.Perm (M :: Mss)⌝ -∗
        A.inv s Mss -∗ (∀ P, M P ={∅}=∗ P t) -∗
        |={∅}=> ∃ t' s' Ms' M', ⌜C t' s'⌝ ∗ A.inv s' Ms' ∗
          bi_close Eq (λ t'' => iprop(∀ P, M' P ={∅}=∗ P t'')) t' ∗
          lfp_tp (wpiConstF H Φ) (M' :: Ms'))) := ⟨
    fun _ _ _ HMs => by cases HMs; rfl
  ⟩
  iintro Htp Hinv Ht
  irevert %t %s %M %Mss %C %Hexec %HMs Hinv Ht
  iapply (lfp_tp_ind (wpiConstF H Φ) (λ Ms => iprop(
    ∀ (t : ITree E R) (s : σ) (M : (ITree E R → PROP) → PROP)
      (Mss : List ((ITree E R → PROP) → PROP)) (C : ITree E R → σ → Prop),
      ⌜exec EH t s C⌝ -∗ ⌜Ms.car.Perm (M :: Mss)⌝ -∗
      A.inv s Mss -∗ (∀ P, M P ={∅}=∗ P t) -∗
      |={∅}=> ∃ t' s' Ms' M', ⌜C t' s'⌝ ∗ A.inv s' Ms' ∗
        bi_close Eq (λ t'' => iprop(∀ P, M' P ={∅}=∗ P t'')) t' ∗
        lfp_tp (wpiConstF H Φ) (M' :: Ms')))) $$ [] %⟨Ms⟩ Htp
  iintro !> %Ms IH %t %s %M %Mss %C %Hexec %HMs Hinv Ht
  rw [← exec.fold] at Hexec
  cases Hexec with
  | stop _ _ _ HC =>
      imodintro; iexists t, s, Mss, M
      isplitr
      · ipureintro; exact HC
      · iframe
        isplitl [Ht]
        · simp only [bi_close]
          iexists t; isplitr
          · ipureintro; rfl
          · iexact Ht
        · iapply (lfp_tp_unfold (wpiConstF H Φ) (M :: Mss)).mpr
          iapply lfp_tpF_perm (wpiConstF H Φ) Ms.car (M :: Mss) _ _ HMs $$ IH
          iintro %Ns1 %Ns2 %Hperm Hrec
          icases Hrec with ⟨-, Htp⟩
          iapply lfp_tp_perm (wpiConstF H Φ) Ns1.car Ns2.car Hperm $$ Htp
  | tau t _ _ Hexec =>
      ihave IH := lfp_tpF_perm_close (wpiConstF H Φ) Ms.car (M :: Mss) _ HMs $$ IH
      have Hlookup : (M :: Mss)[0]? = some M := by simp
      ihave IH := lfp_tpF_lookup (wpiConstF H Φ) _ (M :: Mss) 0 M Hlookup $$ IH
      ihave IH := bi_mono0_mono_l M (λ P => iprop(|={∅}=> P t.tau)) _ $$ IH [Ht]
      · iintro %P HM; iapply Ht $$ %P HM
      imod bi_mono0_elim $$ IH [] with ⟨%G, Hwpi, Hc⟩
      · iintro %Q %Q' Hwand HQ'
        imod HQ'; imodintro; iapply Hwand $$ HQ'
      ihave >Hwpi := (wpiConstF_tau H Φ G t).mp $$ Hwpi
      ihave Hspawn := (BigSepL.bigSepL_singleton
        (x := (λ P : ITree E R → PROP => P t))
        (Φ := λ _ (N : (ITree E R → PROP) → PROP) => N G)).mpr $$ Hwpi
      ispecialize Hc $$ %([λ P => P t]) Hspawn
      simp only [bi_close]
      icases Hc with ⟨%Ns, %Hperm, Hrec⟩
      icases Hrec with ⟨Hadequate, -⟩
      iapply Hadequate $$ %t %s %(λ P => P t) %Mss %C %Hexec %Hperm.symm Hinv []
      iintro %P HP; imodintro; iexact HP
  | step i k _ _ Hhandle =>
      ihave IH := lfp_tpF_perm_close (wpiConstF H Φ) Ms.car (M :: Mss) _ HMs $$ IH
      have Hlookup : (M :: Mss)[0]? = some M := by simp
      ihave IH := lfp_tpF_lookup (wpiConstF H Φ) _ (M :: Mss) 0 M Hlookup $$ IH
      ihave IH := bi_mono0_mono_l M
        (λ P => iprop(|={∅}=> P (.vis i k))) _ $$ IH [Ht]
      · iintro %P HM; iapply Ht $$ %P HM
      imod bi_mono0_elim $$ IH [] with ⟨%G, Hwpi, Hc⟩
      · iintro %Q %Q' Hwand HQ'
        imod HQ'; imodintro; iapply Hwand $$ HQ'
      ihave >Hwpi := (wpiConstF_vis H Φ G i k).mp $$ Hwpi
      imod A.adequate G i s Mss (λ t s => exec EH t s C) k Hhandle $$ Hwpi Hinv with
        ⟨%t', %s', %M', %Ms', %Msn, %HC, %HpermA, Hspawn, Hinv, Hmod⟩
      ispecialize Hc $$ %Msn Hspawn
      simp only [bi_close]
      icases Hc with ⟨%Ns, %HpermClose, Hrec⟩
      icases Hrec with ⟨Hadequate, -⟩
      have Hpool : Ns.car.Perm (M' :: Ms') :=
        (HpermA.trans HpermClose).symm
      iapply Hadequate $$ %t' %s' %M' %Ms' %C %HC %Hpool Hinv Hmod

theorem wpi_adequate (Φ : R → PROP) (H : IHandler PROP E)
    (EH : EHandler E E R σ) [A : EHandlerAdequate (PROP := PROP) H EH]
    (t : ITree E R) (s : σ)
    (C : ITree E R → σ → Prop) (m : CoPset)
    (Hexec : exec EH t s C) :
    ⊢ WPi t @> H;m {{ Φ }} -∗
      A.inv s [] -∗
      |={m, ∅}=> ∃ t' s' Ms' M',
      ⌜C t' s'⌝ ∗
      A.inv s' Ms' ∗
      bi_close Eq (λ t'' => iprop(∀ P, M' P ={∅}=∗ P t'')) t' ∗
      wpi_tp H (M' :: Ms') (λ v => iprop(|={∅,m}=> Φ v)) := by
  iintro Hwpi Hinv
  ihave Hwpi := wpi_fupd_empty $$ Hwpi
  ihave Hwpi := fupd_wpi_empty $$ Hwpi
  imod Hwpi
  ihave Htp := wpi_tp_intro t H (λ v => iprop(|={∅,m}=> Φ v)) $$ Hwpi
  iapply wpi_adequate_ind (λ v => iprop(|={∅,m}=> Φ v)) H EH t s
    [λ P => P t] [] (λ P => P t) C Hexec (List.Perm.refl _) $$ Htp Hinv []
  iintro %P HP; imodintro; iexact HP

end wpi_adequate

end IrisITree.Core
