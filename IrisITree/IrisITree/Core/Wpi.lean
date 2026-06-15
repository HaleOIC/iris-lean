module

import Iris.BI.Lib.Fixpoint
public import Iris.ProofMode.Classes
import Iris.ProofMode
public import ITree.Definition
public import ITree.Effect
public import IrisITree.Core.Handler
import IrisITree.Core.ITree

namespace IrisITree.Core
open Iris Iris.BI ITree

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]

public section

section wp_itree_def


variable {E} (H : IHandler PROP E)

@[expose]
def wpiF {R} (wpi : CoPset → ITree E R → (R → PROP) → PROP) :
    CoPset → CoPset → ITree E R → (R → PROP) → PROP :=
  λ Ms Me t Φ =>
    iprop(
      |={Ms, ∅}=> match t.unfold with
        | ITreeF.ret r => iprop(|={∅, Me}=> Φ r)
        | ITreeF.tau t' => wpi ∅ t' Φ
        | ITreeF.vis i k => H.ihandle i
          (λ a => wpi ∅ (k a) Φ)
          (λ a => wpi ∅ (k a) (λ _ => iprop(|={∅}=> False)))
    )

private def wpiF' {R} (Me : CoPset) (wpi : (LeibnizO CoPset) × ITree E R × (R → PROP) → PROP) :
    (LeibnizO CoPset) × ITree E R × (R → PROP) → PROP :=
  λ ⟨Ms, t, Φ⟩ => wpiF H (λ Ms t Φ => wpi ⟨⟨Ms⟩, t, Φ⟩) Ms.1 Me t Φ

theorem wpiF_mono {R} (wp1 wp2 : CoPset → ITree E R → (R → PROP) → PROP) Me :
    □ (∀ t Φ, wp1 ∅ t Φ -∗ wp2 ∅ t Φ) -∗
    ∀ Ms t Φ, wpiF H wp1 Ms Me t Φ -∗ wpiF H wp2 Ms Me t Φ := by
  iintro #Hwand %Ms %t %Φ Hwp
  unfold wpiF; imod Hwp; imodintro
  cases t.unfold <;> simp
  case ret => iexact Hwp
  case tau t' => iapply Hwand $$ Hwp
  case vis i k =>
    iapply H.ihandle_mono $$ [] [] Hwp
    · iintro %_; iapply Hwand
    · iintro !> %_; iapply Hwand

private instance {R Me} : BIMonoPred (wpiF' (R:=R) H Me) where
  mono_pred := by
    iintro %Φ %Ψ %HΦ %HΨ #H %pair Hsim
    rcases pair with ⟨_, _, _⟩
    simp only [wpiF']
    iapply wpiF_mono $$ [] Hsim
    iintro !> %t %Φ1
    iapply H
  mono_pred_ne := by
    intro wp Hwp; constructor; intro n ⟨Ms1, t1, Ψ1⟩ ⟨Ms2, t2, Ψ2⟩ ⟨HMs, Ht, HΨ⟩
    simp at HMs Ht HΨ; subst HMs Ht
    unfold wpiF'; apply BIFUpdate.ne.ne
    cases t1 <;> simp
    case ret r => apply BIFUpdate.ne.ne; apply HΨ
    case tau t' => apply Hwp.ne; refine ⟨.rfl, .rfl, HΨ⟩
    case vis i k =>
      apply OFE.NonExpansive₂.ne <;> intro a
      · apply Hwp.ne; refine ⟨.rfl, .rfl, HΨ⟩
      · apply Hwp.ne; refine ⟨.rfl, .rfl, .rfl⟩

/-- `wpi` is a weakest precondition for `ITree` -/
def wpi {E R} (H : IHandler PROP E) (Ms Me : CoPset) (t : ITree E R) (Φ : R → PROP) : PROP :=
  bi_least_fixpoint (wpiF' H Me) (⟨Ms⟩, t, Φ)

instance {R Ms Me} {t : ITree E R} : OFE.NonExpansive (wpi H Ms Me t) := by
  constructor; intro n Φ₁ Φ₂ HΦ
  exact OFE.NonExpansive.ne (f := bi_least_fixpoint (wpiF' H Me)) ⟨rfl, rfl, HΦ⟩

end wp_itree_def

-- TODO: This turns }} into a token. Can we somehow prevent this?
macro:max "WPi " t:term:20 " @> " H:term:20 ";" Ms:term:20 "," Me:term:20 " {{ " Φ:term:20 " }}" : term => `(wpi (H := $H) $Ms $Me $t $Φ)
macro:max "WPi " t:term:20 " @> " H:term:20 ";" Ms:term:20 "," Me:term:20 " {{ " v:ident " , " Q:term:20 " }}" : term => `(wpi (H := $H) $Ms $Me $t <| λ $v => $Q)

macro:max "WPi " t:term:20 " @> " H:term:20 ";" M:term:20 " {{ " Φ:term:20 " }}" : term => `(wpi (H := $H) $M $M $t $Φ)
macro:max "WPi " t:term:20 " @> " H:term:20 ";" M:term:20 " {{ " v:ident " , " Q:term:20 " }}" : term => `(wpi (H := $H) $M $M $t <| λ $v => $Q)

delab_rule wpi
  | `($_ $H $Ms $Me $t (fun $v:ident => $Q)) =>
    if Ms == Me then `(WPi $t @> $H;$Ms {{ $v, $Q }})
    else `(WPi $t @> $H;$Ms,$Me {{ $v, $Q }})
  | `($_ $H $Ms $Me $t $Φ) =>
    if Ms == Me then `(WPi $t @> $H;$Ms {{ $Φ }})
    else `(WPi $t @> $H;$Ms, $Me {{ $Φ }})

section wpi_unfold

variable {E} {Ms Me : CoPset} {H : IHandler PROP E}

theorem wpi_unfold {R} (t : ITree E R) Φ :
    WPi t @> H;Ms,Me {{ Φ }} ⊣⊢ wpiF H (λ Ms t Φ => WPi t @> H;Ms,Me {{ Φ }}) Ms Me t Φ := by
  apply equiv_iff.mp
  apply least_fixpoint_unfold

theorem fupd_wpi_empty (Φ : R → PROP) :
    WPi t @> H;Ms,Me {{ Φ }} ⊣⊢ |={Ms, ∅}=> WPi t @> H;∅,Me {{ Φ }} :=
    (wpi_unfold _ _).trans <| by
  unfold wpiF; isplit <;> iintro >Hwp
  · imodintro; iapply wpi_unfold; unfold wpiF; imodintro; iassumption
  · ihave H := wpi_unfold $$ Hwp; unfold wpiF; iassumption

section instances

open ProofMode
instance elimModal_fupd_wpi p E1 E2 E3 (P : PROP) :
    ElimModal True p false
      iprop(|={E1,E2}=> P) P
      iprop(WPi t @> H;E1,E3 {{Φ}}) iprop(WPi t @> H;E2,E3 {{Φ}}) where
  elim_modal _ := by
    cases p <;> simp
    · iintro ⟨HP, Hwand⟩; iapply fupd_wpi_empty
      imod HP; iapply fupd_wpi_empty; iapply Hwand $$ HP
    · iintro ⟨#HP, Hwand⟩; iapply fupd_wpi_empty
      imod HP; iapply fupd_wpi_empty; iapply Hwand $$ HP

instance elimModal_wpi_wpi p H1 H2 (t1 : ITree E1 R1) (t2 : ITree E2 R2) Ms Me1 Me2 Φ1 Φ2 :
    ElimModal (PROP:=PROP) True p false
      iprop(WPi t1 @> H1;Ms,Me1 {{Φ1}}) iprop(WPi t1 @> H1;∅,Me1 {{Φ1}})
      iprop(WPi t2 @> H2;Ms,Me2 {{Φ2}}) iprop(WPi t2 @> H2;∅,Me2 {{Φ2}}) where
  elim_modal _ := by
    cases p <;> simp
    all_goals
      iintro ⟨HΦ, Hwand⟩; ihave HΦ := fupd_wpi_empty $$ HΦ
      iapply fupd_wpi_empty; imod HΦ; imodintro
      iapply Hwand $$ HΦ

instance elimModal_wpi_fupd p E1 E2 E3 (P : PROP) :
    ElimModal True p false
      iprop(WPi t @> H;E1,E3 {{Φ}}) iprop(WPi t @> H;∅,E3 {{Φ}})
      iprop(|={E1,E2}=> P) iprop(|={∅,E2}=> P) where
  elim_modal _ := by
    cases p <;> simp
    all_goals
      iintro ⟨HΦ, Hwand⟩; ihave HΦ := fupd_wpi_empty $$ HΦ
      imod HΦ; iapply Hwand $$ HΦ

end instances

theorem fupd_wpi (Φ : R → PROP) :
    WPi t @> H;Ms,Me {{ Φ }} ⊣⊢ |={Ms}=> WPi t @> H;Ms,Me {{ Φ }} := by
  isplit <;> iintro Hwp
  · imodintro; iframe
  · imod Hwp; iframe

theorem wpi_pure' {R} (Φ : R → PROP) (r : R) :
  WPi pure r @> H;Ms,Me {{ Φ }} ⊣⊢ (|={Ms, Me}=> Φ r) := (wpi_unfold _ _).trans <| by
  simp [wpiF]
  isplit
  · iintro >$
  · iintro >_; iapply fupd_mask_intro
    · simp
    iintro >Hemp !>; iframe

theorem wpi_pure {R} (M : CoPset) (Φ : R → PROP) (r : R) :
    Φ r ⊢ WPi pure r @> H; M {{ Φ }} := by
  iintro HΦ; iapply wpi_pure'; imodintro; iexact HΦ

theorem wpi_tau {R} (Φ : R → PROP) (t : ITree E R) :
    (WPi t.tau @> H;Ms,Me {{ Φ }}) ⊣⊢ (WPi t @> H;Ms,Me {{ Φ }}) := (wpi_unfold _ _).trans <| by
  simp [wpiF]
  isplit <;> iintro >$ //

theorem wpi_vis {R} (Φ : R → PROP) (i : E.I) (k : E.O i → ITree E R) :
    (WPi (ITree.vis i k) @> H;Ms,Me {{ Φ }}) ⊣⊢
    (|={Ms, ∅}=> H.ihandle i
      (λ a => WPi (k a) @> H; ∅,Me {{ Φ }})
      (λ a => WPi (k a) @> H; ∅,Me {{ λ _ => iprop(|={∅}=> False) }})) :=
  wpi_unfold _ _

theorem wpi_trigger_bind {E' A} [E' -< E] (H' : IHandler PROP E') [InH H' H]
    (i : E'.I) (k : E'.O i → ITree E A) (Φ : A → PROP) :
    (|={Ms, ∅}=> H'.ihandle i
      (λ a => WPi (k a) @> H; ∅,Me {{ Φ }})
      (λ a => WPi (k a) @> H; ∅,Me {{ λ _ => iprop(|={∅}=> False) }})) -∗
    WPi E'.trigger i >>= k @> H; Ms, Me {{ Φ }} := by
  iintro >HH; simp [Effect.trigger]
  iapply wpi_vis; imodintro
  iapply H.ihandle_mono; rotate_left 2
  · iapply InH.is_inH $$ HH
  · iintro %r $
  · iintro !> %a $

theorem wpi_trigger {E'} [E' -< E] (H' : IHandler PROP E') [InH H' H]
    (i : E'.I) (Φ : E'.O i → PROP) :
    (|={Ms, ∅}=> H'.ihandle i
      (λ a => iprop(|={∅, Me}=> Φ a))
      (λ _ => iprop(False))) -∗
    WPi (E'.trigger i) @> H; Ms,Me {{ Φ }} := by
  iintro HH; unfold Effect.trigger
  iapply wpi_vis; imod HH; imodintro
  iapply H.ihandle_mono
  · iintro %r HΦ; iapply wpi_pure'; iexact HΦ
  · iintro !> %a Hfalse; icases Hfalse with ⟨⟩
  · iapply InH.is_inH $$ HH

end wpi_unfold

section wpi_induction

variable {E R} {Ms Me : CoPset} {H : IHandler PROP E}

-- TODO: Is this version ever useful?
theorem wpi_ind_mask (G : CoPset → ITree E R → (R → PROP) → PROP)
   [∀ Ms t, OFE.NonExpansive (G Ms t)] :
    □ (∀ Ms t Φ, wpiF H (λ Ms' t' Ψ => iprop(G Ms' t' Ψ ∧ WPi t' @> H;Ms',Me {{ Ψ }})) Ms Me t Φ -∗ G Ms t Φ) ⊢
    ∀ Ms t Φ, WPi t @> H;Ms,Me {{ Φ }} -∗ G Ms t Φ := by
  iintro #HPre %Ms %t %Φ Hwp; unfold wpi
  let G' : (LeibnizO CoPset × _ × _) → _ := λ ⟨⟨Ms⟩, t, Φ⟩ => G Ms t Φ
  have : OFE.NonExpansive G' := by sorry
  iapply least_fixpoint_ind (wpiF' H Me) G' $$ [] %⟨⟨Ms⟩, t, Φ⟩ Hwp
  iintro !> %p HwpiF
  rcases p with ⟨⟨_⟩, _, _⟩
  simp only [wpiF', G']
  iapply HPre
  iapply wpiF_mono $$ [] HwpiF
  iintro !> %_ %_ $

variable (G : ITree E R → (R → PROP) → PROP) [∀ t, OFE.NonExpansive (G t)]

theorem wpi_ind :
    □ (∀ t Φ, wpiF H (λ Ms' t' Ψ => iprop(G t' Ψ ∧ WPi t' @> H;Ms',Me {{ Ψ }})) ∅ Me t Φ -∗ G t Φ) ⊢
    ∀ t Φ, WPi t @> H;∅,Me {{ Φ }} -∗ G t Φ := by
  iintro #HPre %t %Φ Hwp
  let G' := λ (Ms : CoPset) t Φ => iprop(<affine> ⌜Ms = ∅⌝ -∗ G t Φ)
  have : ∀ Ms t, OFE.NonExpansive (G' Ms t) := by sorry
  iapply wpi_ind_mask G' $$ [] Hwp; rotate_left 1; itrivial
  iintro !> %Ms %t %Φ Hwpi %hp; subst hp
  iapply HPre
  iapply wpiF_mono $$ [] Hwpi
  iintro !> %_ %_ HG
  isplit
  · icases HG with ⟨HG, -⟩; iapply HG $$ [//]
  · icases HG with ⟨-, $⟩

theorem wpi_iter :
    □ (∀ t Φ, wpiF H (λ _ => G) ∅ Me t Φ -∗ G t Φ) ⊢
    ∀ t Φ, WPi t @> H;∅,Me {{ Φ }} -∗ G t Φ := by
  iintro #HRet %t %Φ
  iapply wpi_ind $$ []
  iintro !> %t %Φ HwpiF
  iapply HRet
  iapply wpiF_mono $$ [] HwpiF
  iintro !> %_ %_ ⟨$, -⟩

theorem wpi_iter' :
    □ (∀ Φ r, (|={∅, Me}=> Φ r) -∗ G (pure r) Φ) -∗
    □ (∀ Φ t, (|={∅}=> G t Φ) -∗ G (ITree.tau t) Φ) -∗
    □ (∀ Φ i k, (|={∅}=> H.ihandle i
         (λ a => G (k a) Φ)
         (λ a => G (k a) (λ _ => iprop(|={∅}=> False)))) -∗
           G (ITree.vis i k) Φ) -∗
    ∀ t Φ, WPi t @> H;∅,Me {{ Φ }} -∗ G t Φ := by
  iintro #HPure #HTau #HVis %t %Φ
  iapply wpi_iter $$ []
  iintro !> %t %Φ HwpiF; unfold wpiF
  cases t <;> simp
  · iapply HPure; imod HwpiF with $
  · iapply HTau $$ [$]
  · iapply HVis $$ [$]

end wpi_induction

section wpi_lemmas

variable {E R} {Ms Me : CoPset} {H : IHandler PROP E}

theorem wpi_wand (Φ Ψ : R → PROP) :
    WPi t @> H;Ms,Me {{ Φ }} -∗
    (∀ r, Φ r -∗ Ψ r) -∗
    WPi t @> H;Ms,Me {{ Ψ }} := by
  iintro >Hwp Hwand
  let G := λ t (Φ : R → PROP) =>
    iprop(∀ Ψ, (∀ r, Φ r -∗ Ψ r) -∗ WPi t @> H;∅,Me {{ Ψ }})
  have : ∀ t, OFE.NonExpansive (G t) := by
    intro t; constructor
    intro n x₁ x₂ Hx; simp [G]
    refine forall_ne λ Ψ => wand_ne.ne ?_ .rfl
    exact forall_ne λ r => wand_ne.ne (Hx r) .rfl
  iapply wpi_iter' G $$ [] [] [] Hwp Hwand
  · iintro !> %Φ %r >Hwpi %Ψ Hwand
    iapply wpi_pure; iapply Hwand $$ [$]
  · iintro !> %Φ %t >Hwpi %Ψ Hwand
    iapply wpi_tau; iapply Hwpi $$ Hwand
  · iintro !> %Φ %i %k >Hwpi %Ψ Hwand
    iapply wpi_vis; imodintro
    iapply H.ihandle_mono $$ [Hwand] [] Hwpi
    · iintro %_ HG; iapply HG $$ Hwand
    · iintro !> %_ HG; iapply HG; iintro %_ >⟨⟩

theorem wpi_fupd_empty (Φ : R → PROP) :
    (WPi t @> H; Ms, Me {{ Φ }}) ⊣⊢
    (WPi t @> H; Ms, ∅ {{ v, iprop(|={∅, Me}=> Φ v) }})
     := by
  isplit <;> iintro >Hwp
  · let G := λ t (Ψ : R → PROP) =>
      WPi t @> H; ∅,∅ {{ v, iprop(|={∅, Me}=> Ψ v) }}
    have : ∀ t, OFE.NonExpansive (G t) := by
      intro t; constructor
      intro n Ψ₁ Ψ₂ HΨ; simp [G]
      exact OFE.NonExpansive.ne (f := wpi H ∅ ∅ t) <|
        λ v => BIFUpdate.ne.ne (HΨ v)
    iapply wpi_iter' G $$ [] [] [] Hwp
    · iintro !> %Ψ %r HΨ; simp [G]
      iapply wpi_pure; iframe
    · iintro !> %Ψ %t >HΨ
      iapply wpi_tau; iframe
    · iintro !> %Ψ %i %k >HΨ; simp [G]
      iapply wpi_vis; imodintro
      iapply H.ihandle_mono $$ [] [] HΨ
      · iintro %_ $
      · iintro !> %_ _
        iapply wpi_wand $$ [$]
        iintro %_ > Hf
        imod fupd_mask_subseteq (E2:=∅); simp
        imod Hf with ⟨⟩
  · let G := λ t (Ψ : R → PROP) =>
      iprop(∀ Φ, (∀ r, Ψ r -∗ |={∅, Me}=> Φ r) -∗ WPi t @> H;∅,Me {{ Φ }})
    have : ∀ t, OFE.NonExpansive (G t) := by
      intro t; constructor
      intro n Ψ₁ Ψ₂ HΨ; simp [G]
      refine forall_ne λ Φ => wand_ne.ne ?_ .rfl
      exact forall_ne λ r => wand_ne.ne (HΨ r) .rfl
    iapply wpi_iter' G $$ [] [] [] Hwp
    · iintro !> %Ψ %r >HΨ %Φ Hwand
      iapply wpi_pure'
      iapply Hwand $$ HΨ
    · iintro !> %Ψ %t >HΨ %Φ Hwand
      iapply wpi_tau
      iapply HΨ $$ Hwand
    · iintro !> %Ψ %i %k >HΨ %Φ Hwand
      iapply wpi_vis
      imodintro
      iapply H.ihandle_mono $$ [Hwand] [] HΨ
      · iintro %_ HG
        iapply HG $$ Hwand
      · iintro !> %_ HG
        iapply HG
        iintro %_ Hfalse
        icases Hfalse with >⟨⟩
    · iintro %r $

theorem wpi_fupd (Φ : R → PROP) :
    (WPi t @> H; Ms, Me {{ Φ }}) ⊣⊢
    (WPi t @> H; Ms, Me {{ v, iprop(|={Me}=> Φ v) }})
     := by
  isplit <;> iintro Hwp
  · iapply wpi_wand $$ Hwp; iintro %_ $ //
  · iapply wpi_fupd_empty
    iapply wpi_wand $$ [Hwp]
    · iapply (wpi_fupd_empty (Me:=Me)) $$ Hwp
    iintro %_ > > $ //

theorem wpi_bind' {A} M' t (k : A → ITree E R) (Φ : R → PROP) :
    WPi t @> H; Ms, M' {{ r, WPi k r @> H;M',Me {{ Φ }} }} ⊢
    WPi t >>= k @> H; Ms, Me {{ Φ }} := by
  iintro >Hwp
  let G := λ t (Φ : A → PROP) =>
    iprop(∀ Ψ, (∀ r, Φ r -∗ WPi k r @> H; M', Me {{ Ψ }})
      -∗ WPi t >>= k @> H; ∅, Me {{ Ψ }})
  have : ∀ t, OFE.NonExpansive (G t) := by sorry
  iapply wpi_iter' G $$ [] [] [] Hwp
  rotate_right 1; focus iintro %_ $
  · iintro !> %Φ %r >Hwpi %Ψ Hwand; simp
    iapply Hwand $$ [$]
  · iintro !> %Φ %t >Hwpi %Ψ Hwand; simp
    iapply wpi_tau; iapply Hwpi $$ Hwand
  · iintro !> %Φ %i %k >Hwpi %Ψ Hwand; simp
    iapply wpi_vis; imodintro
    iapply H.ihandle_mono $$ [Hwand] [] Hwpi
    · iintro %_ HG; iapply HG $$ Hwand
    · iintro !> %_ HG; iapply HG; iintro %_ Hf
      imod fupd_mask_subseteq (E2 := ∅); simp
      imod Hf with ⟨⟩

-- specialized version where M' = Ms. This is especially useful for the Ms = Me case.
theorem wpi_bind {A} t (k : A → ITree E R) (Φ : R → PROP) :
    WPi t @> H; Ms {{ r, WPi k r @> H;Ms,Me {{ Φ }} }} ⊢
    WPi t >>= k @> H; Ms, Me {{ Φ }} := wpi_bind' _ _ _ _

end wpi_lemmas

section wp_itree_invariant

-- TODO: Invariant rules from the Coq development are omitted for now.
-- This Lean repository does not yet expose an invariant API with
-- `inv`, `inv_acc`, or `inv_acc_timeless`, so the corresponding masked
-- WPi lemmas cannot be stated here yet.

end wp_itree_invariant


section wp_itree_translation

-- `f` can interpret each event `E1` as an `itree E2 E1.I`, as a way to
-- "translate" from events `E1` to `E2`
variable {E1 E2 : Effect} {Ms Me : CoPset}
  {PROP : Type _} [BI PROP] [BIFUpdate PROP]
  {H1 : IHandler PROP E1} {H2 : IHandler PROP E2}
  (f : (i : E1.I) → ITree E2 (E1.O i))

/-- Translate a WPi proof across handlers by interpreting each `E₁` event as an `E₂` itree. -/
theorem wpi_translation {R} (t : ITree E1 R) (Φ : R → PROP) :
    WPi t @> H1; Ms, Me {{ Φ }} -∗
    □ (∀ i (k : E1.O i → ITree E1 R) Ψ,
      H1.ihandle i
        (λ a => WPi (ITree.interp f (k a)) @> H2; ∅,Me {{ Ψ }})
        (λ a => WPi (ITree.interp f (k a)) @> H2; ∅,Me {{ λ _ => iprop(|={∅}=> False) }}) -∗
      WPi (f i >>= λ a => ITree.interp f (k a)) @> H2; ∅,Me {{ Ψ }}) -∗
    WPi (ITree.interp f t) @> H2; Ms, Me {{ Φ }} := by
  iintro >Hwp #HH
  let G : ITree E1 R → (R → PROP) → PROP := λ t Φ => WPi (ITree.interp f t) @> H2; ∅,Me {{Φ}}
  iapply (wpi_iter' G) $$ [] [] [] Hwp
  · iintro !> %Φ %r >Hret; simp
    iapply wpi_pure $$ Hret
  · iintro !> %Φ %t >Htau; simp [interp_tau]
    iapply wpi_tau $$ Htau
  · iintro !> %Φ %i %k >Hvis; simp[interp_vis]
    iapply HH $$ Hvis

/-- A sequential special case of `wpi_translation` with a simpler handler-side premise. -/
theorem wpi_translation_seq {R} (t : ITree E1 R) (Φ : R → PROP) :
    WPi t @> H1; Ms,Me {{ Φ }} -∗
    □ (∀ i Ψ, H1.ihandle i Ψ (λ _ => iprop(True)) -∗
        WPi (f i) @> H2; ∅ {{ Ψ }}) -∗
    WPi (ITree.interp f t) @> H2; Ms,Me {{ Φ }} := by
  iintro Hwp #Hwand; iapply wpi_translation $$ Hwp
  iintro !> %i %k %Ψ Hh; iapply wpi_bind; iapply Hwand
  iapply H1.ihandle_mono $$ [] [] Hh
  · iintro %a $
  · iintro !> %t Hwp; exact true_intro

end wp_itree_translation

section wp_itree_mono

variable {E : Effect} {Ms Me : CoPset}
  {PROP : Type _} [BI PROP] [BIFUpdate PROP]
  {H1 : IHandler PROP E} {H2 : IHandler PROP E}
  [Hwand : WandH H1 H2]

theorem wpi_wandH {R} (t : ITree E R) (Φ : R → PROP) :
    WPi t @> H1; Ms, Me {{ Φ }} ⊢ WPi t @> H2; Ms, Me {{ Φ }} := by
  iintro Hwp
  have ht : t = t.interp (λ i => E.trigger i) := by simp
  rw (occs:=[2]) [ht]
  iapply wpi_translation $$ Hwp
  iintro !> %i %k %Ψ Hh
  simp [Effect.trigger]; iapply wpi_vis; imodintro
  iapply Hwand.is_wandH
  iapply H1.ihandle_mono i $$ [] [] Hh
  · iintro %a $
  · iintro !> %a $

end wp_itree_mono

section wp_itree_inH

variable {E1 E2 : Effect} {Ms Me : CoPset}
  {PROP : Type _} [BI PROP] [BIFUpdate PROP] [BIAffine PROP]
  {H1 : IHandler PROP E1} {H2 : IHandler PROP E2}
  [sub : E1 -< E2] [Hin : InH H1 H2]

theorem wpi_inH {R} (t : ITree E1 R) (Φ : R → PROP) :
    (WPi t @> H1; Ms, Me {{ Φ }}) ⊣⊢
    (WPi (t.interp (λ i => E1.trigger i)) @> H2; Ms, Me {{ Φ }}) := by
  isplit <;> iintro Hwp
  · iapply wpi_translation $$ Hwp
    iintro !> %i %k %Ψ Hh
    iapply wpi_trigger_bind; imodintro
    iapply H1.ihandle_mono $$ [] [] Hh
    · iintro %a $
    · iintro !> %a $
  · let emb : (i : E1.I) → ITree E2 (E1.O i) := fun i => E1.trigger i
    let G : ITree E2 R → (R → PROP) → PROP := λ u Ψ =>
      iprop(∀ t', ⌜ITree.interp emb t' = u⌝ -∗ (WPi t' @> H1; ∅ {{ Ψ }}))
    ihave Hgen : (∀ u Ψ, (WPi u @> H2; ∅ {{ Ψ }}) -∗ G u Ψ) $$ []
    sorry
    sorry
    -- · iapply wpi_iter' G
    --   · intro u; constructor; intro n Ψ₁ Ψ₂ HΨ
    --     simp [G]; apply forall_ne; intro t'
    --     exact wand_ne.ne .rfl <| (wpi_ne ∅ H1 t').ne HΨ
    --   · iintro !> %Ψ %r HΦ; simp [G]; iintro %t' %Heq
    --     iapply fupd_wpi; imod HΦ; imodintro
    --     have Heq' := interp_ret_inv Heq; subst Heq'
    --     iapply wpi_ret $$ HΦ
    --   · iintro !> %Ψ %u Hu; simp [G]; iintro %t' %Heq
    --     iapply fupd_wpi; imod Hu; imodintro
    --     rcases interp_tau_inv Heq with ⟨t1, rfl, Heq1⟩
    --     iapply wpi_tau ∅ Ψ t1; iapply Hu $$ %t1 %Heq1
    --   · iintro !> %Ψ %i %k Hik; simp [G]; iintro %t' %Heq
    --     rcases interp_vis_inv Heq with ⟨i', k', Ht', Hi, Hk⟩
    --     subst Ht'; iapply wpi_vis; imod Hik; imodintro
    --     iapply Hin.is_inH; subst Hi;
    --     iapply H2.ihandle_mono (Subeffect.map i').fst $$ [] [] Hik
    --     · iintro %a HG; iapply wpi_fupd; iapply HG;
    --       ipure_intro; subst Hk; rfl
    --     · iintro !> %a HG; iapply wpi_atomic_false; iapply HG
    --       ipure_intro; subst Hk; rfl
    -- iapply Hgen $$ Hwp %t %rfl

end wp_itree_inH
