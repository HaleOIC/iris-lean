module

public import IrisITree.Core.Handler
public import IrisITree.Core.ITree
public import IrisITree.Core.Wpi
public import Iris.ProofMode
public import Iris.BI.Lib.Fixpoint
public import ITree.Definition
public import ITree.Effect

@[expose] public section

open Iris BI ITree

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]

section wpi_tree_mask_def

variable {E} (M : CoPset) (H : IHandler (PROP := PROP) E)

open OFE

def wpi_mask (t : ITree E R) (Φ : R → PROP) : PROP :=
  iprop(|={M,∅}=> wpi H t (λ v => iprop(|={∅,M}=> Φ v)))

instance wpi_mask_ne (t : ITree E R) :
    OFE.NonExpansive (λ Φ => wpi_mask (H := H) M t Φ) := by
  constructor
  intro n Φ₁ Φ₂ HΦ
  apply BIFUpdate.ne.ne
  apply NonExpansive.ne
  exact λ v => BIFUpdate.ne.ne (HΦ v)

end wpi_tree_mask_def

macro:20 "WPi " t:term:20 " @> " H:term:20 "; " M:term:20 " {{ " Φ:term:20 " }}" : term => `(wpi_mask (H := $H) $M $t $Φ)
macro:20 "WPi " t:term:20 " @> " H:term:20 "; " M:term:20 " {{ " v:ident " , " Q:term:20 " }}" : term => `(wpi_mask (H := $H) $M $t <| λ $v => $Q)

delab_rule wpi_mask
  | `($_ $M $H $t (fun $v:ident => $Q)) => `(WPi $t @> $H;$M {{ $v, $Q }})
  | `($_ $M $H $t $Φ) => `(WPi $t @> $H;$M {{ $Φ }})

section wpi_tree_mask_def

open OFE

variable {E} {M : CoPset} {H : IHandler (PROP := PROP) E}

theorem wpi_empty_mask_equiv {R} (t : ITree E R) (Φ : R → PROP) :
    (WPi t @> H;∅ {{ Φ }}) ⊣⊢ (WPi t @> H {{ Φ }}) :=
  (equiv_iff.mp <| BIFUpdate.ne.eqv <| equiv_iff.mpr <|
    wpi_update_post_emp_mask H t).trans <| wpi_update_emp_mask H Φ t

theorem wpi_unfold {R} (t : ITree E R) Φ :
    (WPi t @> H;∅ {{ Φ }}) ⊣⊢ ((wpiF H <| λ t Φ => WPi t @> H;∅ {{ Φ }}) t Φ) := by
  apply (wpi_empty_mask_equiv t Φ).trans; apply (wpi_unfold_emp_mask H t Φ).trans
  isplit <;> iintro Hwp
  · iapply wpiF_mono (H := H) <| wpi H $$ [] Hwp
    iintro !> %t %Φ Hwp; iapply (wpi_empty_mask_equiv (H := H) t Φ).mpr $$ Hwp
  · iapply wpiF_mono (H := H) _ <| wpi H $$ [] Hwp
    iintro !> %t %Φ Hwp; iapply (wpi_empty_mask_equiv (H := H) t Φ).mp $$ Hwp

instance wpi_ne {R} (t : ITree E R) : NonExpansive (λ Φ => WPi t @> H; M {{ Φ }}) :=
  wpi_mask_ne M H t

theorem wpi_mask_post_congr (t : ITree E R) {Φ Ψ : R → PROP}
    (HΦ : Φ ≡ Ψ) :
    (WPi t @> H; M {{ Φ }}) ⊣⊢ (WPi t @> H; M {{ Ψ }}) :=
  equiv_iff.mp <| NonExpansive.eqv (f := λ Φ => WPi t @> H; M {{ Φ }}) HΦ

end wpi_tree_mask_def

-- Induction principles for WPi (mask version)
section wp_itree_induction

open OFE ITree

variable {E R} {H : IHandler (PROP := PROP) E} (G : ITree E R → (R → PROP) → PROP)

theorem wpi_ind : (∀ t, NonExpansive (G t)) →
    □ (∀ t Φ, wpiF H (λ t' Ψ => iprop(G t' Ψ ∧ (WPi t' @> H;∅ {{ Ψ }}))) t Φ -∗ G t Φ) ⊢
    ∀ t Φ, (WPi t @> H;∅ {{ Φ }}) -∗ G t Φ := by
  iintro %Hne #HPre %t %Φ Hwp
  iapply wpi_ind_emp_mask H G Hne
  · iintro !> %t %Φ Hx; iapply HPre; iapply wpiF_mono H <| λ t' Ψ => iprop(G t' Ψ ∧ (WPi t' @> H {{ Ψ }}))
    · iintro !> %t' %Φ' Hpair; isplit
      · iapply and_elim_l $$ Hpair
      · iapply wpi_empty_mask_equiv; iapply and_elim_r $$ Hpair
    · iexact Hx
  · iapply wpi_empty_mask_equiv $$ Hwp

theorem wpi_iter : (∀ t, NonExpansive (G t)) →
    □ (∀ t Φ, wpiF H G t Φ -∗ G t Φ) ⊢
    ∀ t Φ, (WPi t @> H;∅ {{ Φ }}) -∗ G t Φ := by
  iintro %Hne #HRet %t %Φ Hwp
  iapply wpi_iter_emp_mask H G Hne $$ HRet
  iapply wpi_empty_mask_equiv $$ Hwp

theorem wpi_iter' : (∀ t, OFE.NonExpansive (G t)) →
    ⊢ □ (∀ Φ r, (|={∅}=> Φ r) -∗ G (ret r) Φ) -∗
      □ (∀ Φ t, (|={∅}=> G t Φ) -∗ G (tau t) Φ) -∗
      □ (∀ Φ i k, (|={∅}=> H.ihandle i
          (λ a => G (k a) Φ)
          (λ a => iprop(|={⊤,∅}=> G (k a) (λ _ => iprop(False))))) -∗
            G (vis i k) Φ) -∗
      ∀ t Φ, (WPi t @> H;∅ {{ Φ }}) -∗ G t Φ := by
  iintro %Hne #HRet #HTau #HVis %t %Φ Hwp
  iapply wpi_iter_emp_mask' H G Hne $$ HRet HTau HVis
  iapply wpi_empty_mask_equiv $$ Hwp

end wp_itree_induction

section wp_itree_derived

open ITree BIUpdate OFE

variable {E R} {H : IHandler (PROP := PROP) E} (t : ITree E R)

theorem wpi_wand (M : CoPset) (Φ Ψ : R → PROP) :
    (∀ r, iprop(Φ r -∗ Ψ r)) ⊢
    (WPi t @> H; M {{ Φ }}) -∗ (WPi t @> H; M {{ Ψ }}) := by
  iintro Hwand Hwp; unfold wpi_mask; imod Hwp; imodintro;
  iapply wpi_wand_emp_mask _ _  <| λ v => iprop(|={∅,M}=> Φ v) $$ [Hwand] Hwp
  iintro %r HΦ; imod HΦ; imodintro; iapply Hwand $$ HΦ

theorem wpi_bind {A} (t : ITree E A) (k : A → ITree E R) (M : CoPset) (Φ : R → PROP) :
    (WPi t @> H; M {{ r, WPi (k r) @> H; M {{ Φ }} }}) ⊢
    (WPi (t >>= k) @> H; M {{ Φ }}) := by
  iintro Hwp; unfold wpi_mask; imod Hwp; imodintro
  iapply wpi_bind_emp_mask; simp
  iapply wpi_wand_emp_mask _ _ <| λ v => iprop(|={∅,M}=> |={M,∅}=>
    WPi k v @> H {{ λ v => iprop(|={∅,M}=> Φ v) }}) $$ [] Hwp
  iintro %r Hwp; iapply wpi_update_emp_mask; imod Hwp; imod Hwp; imodintro; iexact Hwp

theorem fupd_wpi (M : CoPset) (Φ : R → PROP) :
    (|={M}=> WPi t @> H; M {{ Φ }}) ⊣⊢
    (WPi t @> H; M {{ Φ }}) := by
  isplit <;> iintro Hwp
  · unfold wpi_mask; imod Hwp; iexact Hwp
  · imodintro; iexact Hwp

theorem wpi_fupd (M : CoPset) (Φ : R → PROP) :
    (WPi t @> H; M {{ v, iprop(|={M}=> Φ v) }}) ⊣⊢
    (WPi t @> H; M {{ Φ }}) := by
  isplit <;> iintro Hwp <;> unfold wpi_mask <;> simp <;> imod Hwp <;> imodintro;
  · iapply wpi_wand_emp_mask H t <| λ v => iprop(|={∅,M}=> |={M}=> Φ v) $$ [] Hwp
    iintro %r Hwp; imod Hwp; iexact Hwp
  · iapply wpi_wand_emp_mask H t λ v => iprop(|={∅,M}=> Φ v) $$ [] Hwp
    iintro %r Hwp; imod Hwp; imodintro; imodintro; iexact Hwp

end wp_itree_derived

section wp_itree_mask_manipulation

open ITree BIUpdate OFE

variable {E R} {H : IHandler (PROP := PROP) E}

theorem wpi_shift_mask (M' M : CoPset) (Φ : R → PROP) (t : ITree E R) :
    ⊢ (|={M, M'}=> WPi t @> H; M' {{ v, iprop(|={M', M}=> Φ v) }}) -∗
      (WPi t @> H; M {{ Φ }}) := by
  iintro Hwp; unfold wpi_mask; simp; imod Hwp; imod Hwp; imodintro
  iapply wpi_wand_emp_mask H t <| λ v => iprop(|={∅,M'}=> |={M',M}=> Φ v) $$ [] Hwp
  iintro %r Hwp; imod Hwp; iexact Hwp

theorem wpi_atomic (M : CoPset) (Φ : R → PROP) (t : ITree E R) :
    (|={M, ∅}=> WPi t @> H; ∅ {{ v, iprop(|={∅, M}=> Φ v) }}) ⊣⊢
    (WPi t @> H; M {{ Φ }}) := by
  isplit <;> iintro Hwp
  · iapply wpi_shift_mask ∅ $$ Hwp
  · unfold wpi_mask; imod Hwp; imodintro; imodintro
    iapply wpi_wand_emp_mask H t <| λ v => iprop(|={∅, M}=> Φ v) $$ [] Hwp
    iintro %r Hwp; simp; imodintro; iexact Hwp

theorem wpi_atomic_false (M : CoPset) (t : ITree E R) :
    ⊢ (|={M, ∅}=> WPi t @> H; ∅ {{ λ _ => iprop(False) }}) -∗
      (WPi t @> H; M {{ λ _ => iprop(False) }}) := by
  iintro Hwp; iapply wpi_atomic; imod Hwp; imodintro
  iapply wpi_wand t ∅ <| λ x => iprop(False) $$ [] Hwp
  iintro %r Hwp; icases Hwp with ⟨⟩

theorem wpi_mask_mono (M M' : CoPset) (Φ : R → PROP) (t : ITree E R) :
    M ⊆ M' →
    ⊢ (WPi t @> H; M {{ Φ }}) -∗
      (WPi t @> H; M' {{ Φ }}) := by
  iintro %Hsubset Hwp; iapply wpi_shift_mask M
  iapply fupd_mask_intro
  · assumption
  · iintro Hemp; iapply wpi_wand t M Φ $$ [Hemp] Hwp
    iintro %r HΦ; imod Hemp; imodintro; iexact HΦ

end wp_itree_mask_manipulation

section wp_itree_invariant

-- TODO: Invariant rules from the Coq development are omitted for now.
-- This Lean repository does not yet expose an invariant API with
-- `inv`, `inv_acc`, or `inv_acc_timeless`, so the corresponding masked
-- WPi lemmas cannot be stated here yet.

end wp_itree_invariant

section wp_itree_stepping

open ITree BIUpdate OFE

variable {E} {H : IHandler (PROP := PROP) E}

theorem wpi_ret' {R} (M : CoPset) (Φ : R → PROP) (r : R) :
    (|={M}=> Φ r) ⊣⊢
    (WPi ret r @> H; M {{ Φ }}) := by
  unfold wpi_mask; isplit
  · iintro HΦ; imod HΦ; iapply fupd_mask_intro
    · exact Std.LawfulSet.empty_subset
    · iintro Hemp; iapply wpi_ret_emp_mask; imod Hemp; imodintro; iexact HΦ
  · iintro Hwp; imod Hwp; iapply BIFUpdate.trans
    iapply wpi_ret_emp_mask' $$ Hwp

theorem wpi_ret {R} (M : CoPset) (Φ : R → PROP) (r : R) :
    Φ r ⊢ (WPi ret r @> H; M {{ Φ }}) := by
  iintro HΦ; iapply wpi_ret'; imodintro; iexact HΦ

theorem wpi_tau {R} (M : CoPset) (Φ : R → PROP) (t : ITree E R) :
    (WPi t @> H; M {{ λ v => Φ v }}) ⊣⊢
    (WPi (tau t) @> H; M {{ Φ }}) := by
  unfold wpi_mask; simp; isplit <;> iintro Hwp <;> (imod Hwp; imodintro)
  · iapply wpi_tau_emp_mask $$ Hwp
  · iapply wpi_tau_emp_mask; iexact Hwp

theorem wpi_vis' {R} (M : CoPset) (Φ : R → PROP) (i : E.I) (k : E.O i → ITree E R) :
    (|={M, ∅}=> H.ihandle i
      (λ a => WPi (k a) @> H; ∅ {{ v, iprop(|={∅, M}=> Φ v) }})
      (λ a => WPi (k a) @> H; ⊤ {{ λ _ => iprop(False) }})) ⊣⊢
    (WPi (vis i k) @> H; M {{ Φ }}) := by
  unfold wpi_mask; simp; isplit
  · iintro Hwp; imod Hwp; imodintro
    iapply wpi_vis_emp_mask; iapply H.ihandle_mono i $$ [] [] Hwp
    · iintro %a Hwp; iapply wpi_update_emp_mask; imod Hwp; imodintro;
      iapply wpi_wand_emp_mask _ _ <| λ v => iprop(|={∅}=> |={∅,M}=> Φ v) $$ [] Hwp
      iintro %r Hwp; imod Hwp; iexact Hwp
    · iintro !> %t Hwp; imod Hwp; imodintro; iapply wpi_update_post_emp_mask
      iapply wpi_wand_emp_mask _ _ <| λ v => iprop(|={∅,⊤}=> False) $$ [] Hwp
      iintro %r Hfalse; imod Hfalse; icases Hfalse with ⟨⟩
  · iintro Hwp; imod Hwp;
    ihave Hhandle := wpi_vis_emp_mask' H (λ v => iprop(|={∅,M}=> Φ v)) i k $$ Hwp
    imod Hhandle; imodintro; iapply H.ihandle_mono $$ [] [] Hhandle
    · iintro %a Hwp; imodintro; iapply wpi_wand_emp_mask $$ [] Hwp
      iintro %r HΦ; imodintro;  iexact HΦ
    · iintro !> %t Hwp; imod Hwp; imodintro; iapply wpi_wand_emp_mask $$ [] Hwp
      iintro %r Hfalse; icases Hfalse with ⟨⟩

theorem wpi_vis {R} (M : CoPset) (Φ : R → PROP) (i : E.I) (k : E.O i → ITree E R) :
    ⊢ (|={M,∅}=> H.ihandle i
      (λ a => WPi (k a) @> H; ∅ {{ v, iprop(|={∅,M}=> Φ v) }})
      (λ a => WPi (k a) @> H; ⊤ {{ λ _ => iprop(False) }})) -∗
      (WPi (vis i k) @> H; M {{ Φ }}) := by
  iintro HH; iapply wpi_vis' M Φ i k $$ HH

theorem wpi_trigger {E'} [E' -< E] (H' : IHandler (PROP := PROP) E') [InH H' H]
    (M : CoPset) (i : E'.I) (Φ : E'.O i → PROP) :
    ⊢ (|={M, ∅}=> H'.ihandle i
      (λ a => iprop(|={∅, M}=> Φ a))
      (λ _ => iprop(False))) -∗
      (WPi (ITree.trigger E' i) @> H; M {{ Φ }}) := by
  iintro HH; unfold ITree.trigger
  iapply wpi_vis; imod HH; imodintro
  iapply H.ihandle_mono
  · iintro %r HΦ; iapply wpi_ret'; imodintro; iexact HΦ
  · iintro !> %a Hfalse; icases Hfalse with ⟨⟩
  · iapply InH.is_inH $$ HH

end wp_itree_stepping

section wp_itree_structural

open ITree BIUpdate OFE

variable {E R} {H : IHandler (PROP := PROP) E} (Φ : R → PROP) (t : ITree E R)

theorem wpi_frame_l (M : CoPset) (P : PROP) :
    ⊢ P ∗ (WPi t @> H; M {{ Φ }}) -∗
      (WPi t @> H; M {{ v, iprop(P ∗ Φ v) }}) := by
  iintro ⟨Hp, Hwp⟩
  iapply wpi_wand t M Φ $$ [Hp]
  · iintro %r Hr; isplitl [Hp]; iexact Hp; iexact Hr
  · iexact Hwp

theorem wpi_frame_r (M : CoPset) (P : PROP) :
    ⊢ (WPi t @> H; M {{ Φ }}) ∗ P -∗
      (WPi t @> H; M {{ v, iprop(Φ v ∗ P) }}) := by
  iintro ⟨Hwp, Hp⟩
  iapply wpi_wand t M Φ $$ [Hp]
  · iintro %r Hr; isplitl [Hr]; iexact Hr; iexact Hp
  · iexact Hwp

end wp_itree_structural

section wp_itree_translation

open ITree BIUpdate OFE

-- `f` can interpret each event `E1` as an `itree E2 E1.I`, as a way to
-- "translate" from events `E1` to `E2`
variable {E1 E2 : Effect} {PROP : Type _} [BI PROP] [BIFUpdate PROP]
  {H1 : IHandler (PROP := PROP) E1} {H2 : IHandler (PROP := PROP) E2}
  (f : (i : E1.I) → ITree E2 (E1.O i))

/-- Translate a WPi proof across handlers by interpreting each `E₁` event as an `E₂` itree. -/
theorem wpi_translation_emp_mask {R} (t : ITree E1 R) (Φ : R → PROP) :
    □ (∀ i (k : E1.O i → ITree E1 R) Ψ,
      H1.ihandle i
        (λ a => WPi (ITree.interp f (k a)) @> H2; ∅ {{ Ψ }})
        (λ a => iprop(|={⊤,∅}=> WPi (ITree.interp f (k a)) @> H2; ∅ {{ λ _ => iprop(False) }})) -∗
      (WPi (f i >>= λ a => ITree.interp f (k a)) @> H2; ∅ {{ Ψ }})) ⊢
    (WPi t @> H1; ∅ {{ Φ }}) -∗
    (WPi (ITree.interp f t) @> H2; ∅ {{ Φ }}) := by
  iintro #HH Hwp
  let G : ITree E1 R → (R → PROP) → PROP := λ t Φ => WPi (ITree.interp f t) @> H2; ∅ {{Φ}}
  iapply (wpi_iter' G) $$ [] [] [] Hwp
  · intro t; apply wpi_ne (interp f t)
  · iintro !> %Φ %r Hret; simp [G, interp_ret];
    iapply wpi_ret' $$ Hret
  · iintro !> %Φ %t Htau; simp [G, interp_tau]
    iapply (wpi_tau ∅ Φ <| interp f t).1; iapply wpi_empty_mask_equiv
    iapply wpi_update_emp_mask; imod Htau; imodintro;
    iapply wpi_empty_mask_equiv; iexact Htau
  · iintro !> %Φ %i %k Hvis; simp[G, interp_vis];
    iapply fupd_wpi; imod Hvis; imodintro
    iapply HH $$ Hvis

theorem wpi_translation {R} (t : ITree E1 R) (M : CoPset) (Φ : R → PROP) :
    □ (∀ i (k : E1.O i → ITree E1 R) Ψ,
      H1.ihandle i
        (λ a => WPi (ITree.interp f (k a)) @> H2; ∅ {{ Ψ }})
        (λ a => WPi (ITree.interp f (k a)) @> H2; ⊤ {{ λ _ => iprop(False) }}) -∗
      (WPi (f i >>= λ a => ITree.interp f (k a)) @> H2; ∅ {{ Ψ }})) ⊢
    (WPi t @> H1; M {{ Φ }}) -∗
    (WPi (ITree.interp f t) @> H2; M {{ Φ }}) := by
  iintro #Hwand Hwp
  iapply wpi_atomic; ihave Hwp := wpi_atomic M Φ $$ Hwp; imod Hwp; imodintro
  iapply wpi_translation_emp_mask (H1 := H1) (H2 := H2) f t <| λ v => iprop(|={∅,M}=> Φ v) $$ [] Hwp
  iintro !> %i %k %Ψ Hh; iapply Hwand; iclear Hwand
  iapply H1.ihandle_mono i $$ [] [] Hh
  · iintro %a Hwp; iexact Hwp
  · iintro !> %t Hwp; iapply wpi_atomic;
    imod Hwp; imodintro; iapply wpi_wand $$ [] Hwp
    iintro %r Hfalse; icases Hfalse with ⟨⟩

/-- A sequential special case of `wpi_translation` with a simpler handler-side premise. -/
theorem wpi_translation_seq {R} (t : ITree E1 R) (M : CoPset) (Φ : R → PROP) :
    □ (∀ i ψ, H1.ihandle i (λ a => ψ a) (λ _ => iprop(True)) -∗
        (WPi (f i) @> H2; ∅ {{ ψ }})) ⊢
    (WPi t @> H1; M {{ Φ }}) -∗
    (WPi (ITree.interp f t) @> H2; M {{ Φ }}) := by
  iintro #Hwand Hwp; iapply wpi_translation $$ [] Hwp
  iintro !> %i %k %Ψ Hh; iapply wpi_bind; iapply Hwand
  iapply H1.ihandle_mono $$ [] [] Hh
  · iintro %a Hwp; iexact Hwp
  · iintro !> %t Hwp; exact true_intro

end wp_itree_translation

section wp_itree_mono

open ITree BIUpdate OFE

variable {E : Effect} {PROP : Type _} [BI PROP] [BIFUpdate PROP]
  {H1 : IHandler (PROP := PROP) E} {H2 : IHandler (PROP := PROP) E}
  [Hwand : WandH H1 H2]

theorem wpi_wandH {R} (M : CoPset) (t : ITree E R) (Φ : R → PROP) :
    (WPi t @> H1; M {{ Φ }}) ⊢ (WPi t @> H2; M {{ Φ }}) := by
  -- TODO: simplify the presence of `H` once we have `irewrite` tactic
  have H : (WPi t @> H1; M {{ Φ }}) ⊢ (WPi interp (λ i => trigger E i) t @> H2; M {{ Φ }}) := by
    iapply wpi_translation; iintro !> %i %k %Ψ Hh
    simp [ITree.trigger]; iapply wpi_vis; imodintro
    iapply Hwand.is_wandH
    iapply H1.ihandle_mono i $$ [] [] Hh
    · iintro %a Hwp
      iapply wpi_empty_mask_equiv; iapply wpi_update_post_emp_mask
      iapply wpi_empty_mask_equiv; iexact Hwp
    · iintro !> %a Hwp
      iexact Hwp
  simpa [interp_trigger_id] using H

end wp_itree_mono

section wp_itree_inH

open ITree BIUpdate OFE

variable {E1 E2 : Effect} {PROP : Type _} [BI PROP] [BIFUpdate PROP] [BIAffine PROP]
  {H1 : IHandler (PROP := PROP) E1} {H2 : IHandler (PROP := PROP) E2}
  [sub : E1 -< E2] [Hin : InH H1 H2]

theorem wpi_inH_emp_mask {R} (t : ITree E1 R) (Φ : R → PROP) :
    (WPi t @> H1; ∅ {{ Φ }}) ⊣⊢
    (WPi (ITree.interp (λ i => ITree.trigger E1 i) t) @> H2; ∅ {{ Φ }}) := by
  isplit <;> iintro Hwp
  · iapply wpi_translation $$ [] Hwp
    iintro !> %i %k %Ψ Hh; simp [ITree.trigger]
    iapply wpi_vis; imodintro
    iapply Hin.is_inH i
      (λ a => WPi interp (λ i => vis (Subeffect.map i).fst λ x =>
        Pure.pure ((Subeffect.map i).snd x)) (k a) @> H2; ∅ {{ v, iprop(|={∅}=> Ψ v) }})
      (λ a => WPi interp (λ i => vis (Subeffect.map i).fst λ x =>
          Pure.pure ((Subeffect.map i).snd x)) (k a) @> H2; ⊤ {{ λ _ => iprop(False) }})
    iapply H1.ihandle_mono i $$ [] [] Hh
    · iintro %a Hwp; iapply wpi_empty_mask_equiv
      iapply wpi_update_post_emp_mask; iapply wpi_empty_mask_equiv
      iexact Hwp
    · iintro !> %a Hwp; iexact Hwp
  · let emb : (i : E1.I) → ITree E2 (E1.O i) := fun i => ITree.trigger E1 i
    let G : ITree E2 R → (R → PROP) → PROP := λ u Ψ =>
      iprop(∀ t', ⌜ITree.interp emb t' = u⌝ -∗ (WPi t' @> H1; ∅ {{ Ψ }}))
    ihave Hgen : (∀ u Ψ, (WPi u @> H2; ∅ {{ Ψ }}) -∗ G u Ψ) $$ []
    · iapply wpi_iter' G
      · intro u; constructor; intro n Ψ₁ Ψ₂ HΨ
        simp [G]; apply forall_ne; intro t'
        exact wand_ne.ne .rfl <| (wpi_mask_ne ∅ H1 t').ne HΨ
      · iintro !> %Ψ %r HΦ; simp [G]; iintro %t' %Heq
        iapply fupd_wpi; imod HΦ; imodintro
        have Heq' := interp_ret_inv Heq; subst Heq'
        iapply wpi_ret $$ HΦ
      · iintro !> %Ψ %u Hu; simp [G]; iintro %t' %Heq
        iapply fupd_wpi; imod Hu; imodintro
        rcases interp_tau_inv Heq with ⟨t1, rfl, Heq1⟩
        iapply wpi_tau ∅ Ψ t1; iapply Hu $$ %t1 %Heq1
      · iintro !> %Ψ %i %k Hik; simp [G]; iintro %t' %Heq
        rcases interp_vis_inv Heq with ⟨i', k', Ht', Hi, Hk⟩
        subst Ht'; iapply wpi_vis; imod Hik; imodintro
        iapply Hin.is_inH; subst Hi;
        iapply H2.ihandle_mono (Subeffect.map i').fst $$ [] [] Hik
        · iintro %a HG; iapply wpi_fupd; iapply HG;
          ipure_intro; subst Hk; rfl
        · iintro !> %a HG; iapply wpi_atomic_false; iapply HG
          ipure_intro; subst Hk; rfl
    iapply Hgen $$ Hwp %t %rfl

theorem wpi_inH {R} (t : ITree E1 R) (M : CoPset) (Φ : R → PROP) :
    (WPi t @> H1; M {{ Φ }}) ⊣⊢
    (WPi (ITree.interp (fun i => ITree.trigger E1 i) t) @> H2; M {{ Φ }}) := by
  isplit <;> (
    iintro Hwp; iapply wpi_atomic; ihave Hwp := wpi_atomic M Φ _ $$ Hwp
    imod Hwp; imodintro; iapply wpi_inH_emp_mask $$ Hwp
  )

end wp_itree_inH
