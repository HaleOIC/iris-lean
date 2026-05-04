module

public import IrisITree.Core.Handler
public import IrisITree.Core.ITree
public import Iris.ProofMode
public import Iris.BI.Lib.Fixpoint
public import ITree.Definition
public import ITree.Effect

@[expose] public section

open Iris BI ITree

section wp_itree_def

variable {E} {PROP : Type _} [BI PROP] [BIFUpdate PROP] (H : IHandler (PROP := PROP) E)

-- The definition of the weakest precondition, prior to taking the fixpoint.
def wpiF {R} (wpi : ITree E R → (R → PROP) → PROP) :
    ITree E R → (R → PROP) → PROP :=
  λ t Φ =>
    iprop(
      |={∅}=> match t.unfold with
        | ITreeF.ret r => Φ r
        | ITreeF.tau t' => wpi t' Φ
        | ITreeF.vis i k => H.ihandle i
          (λ a => wpi (k a) Φ)
          (λ a => iprop(|={⊤,∅}=> wpi (k a) (λ _ => iprop(False))))
    )

def wpiF' {R} (wpi : LeibnizO (ITree E R) × (R → PROP) → PROP) :
    LeibnizO (ITree E R) × (R → PROP) → PROP :=
  λ ⟨t, Φ⟩ => wpiF H (λ t Φ => wpi (⟨t⟩, Φ)) t.car Φ

/-- Helper function for proving BIMonoPred -/
instance wpiF'_ne {R} : OFE.NonExpansive (wpiF' H (R := R)) := by
  constructor
  intro n wp1 wp2 Hwp ⟨t, Φ⟩
  cases h : t.car.unfold <;> simp [wpiF', wpiF, h]
  case tau t' => exact BIFUpdate.ne.ne <| Hwp (⟨t'⟩, Φ)
  case vis i k =>
    apply BIFUpdate.ne.ne
    apply OFE.NonExpansive₂.ne (f := H.ihandle i)
    · intro a; apply Hwp (⟨k a⟩, Φ)
    · intro a; apply BIFUpdate.ne.ne <| Hwp (⟨k a⟩, λ _ => iprop(False))

theorem wpiF_mono {R} (wp1 wp2 : ITree E R → (R → PROP) → PROP) :
    ⊢ □ (∀ t Φ, wp1 t Φ -∗ wp2 t Φ) -∗
      ∀ t Φ, wpiF H wp1 t Φ -∗ wpiF H wp2 t Φ := by
  iintro #Hwand %t %Φ Hwp
  unfold wpiF
  cases t.unfold <;> simp
  case ret => iexact Hwp
  case tau t' => imod Hwp; imodintro; iapply Hwand $$ Hwp
  case vis i k =>
    imod Hwp; imodintro; iapply H.ihandle_mono
    · iintro %a Hk; iapply Hwand $$ Hk
    · iintro !> %a Hk; imod Hk; imodintro; iapply Hwand $$ Hk
    · iexact Hwp

theorem wpiF'_mono {R} (wp1 wp2 : LeibnizO (ITree E R) × (R → PROP) → PROP) :
    ⊢ □ (∀ t Φ, wp1 (t, Φ) -∗ wp2 (t, Φ)) -∗
      ∀ t Φ, wpiF' H wp1 (t, Φ) -∗ wpiF' H wp2 (t, Φ) := by
  simp [wpiF']
  iintro #Hwand %t' %Φ Hwp
  cases t' with | mk t =>
    simp only
    iapply wpiF_mono (wp1 := λ t Φ => wp1 ({ car := t }, Φ)) (wp2 := λ t Φ => wp2 ({ car := t }, Φ))
    · iintro !> %t' %Φ' Hw; iapply Hwand $$ %⟨t'⟩ %Φ' Hw
    · iexact Hwp
/-- End of Helper -/

instance {R} : BIMonoPred (λ wp_itree : LeibnizO (ITree E R) × (R → PROP) → PROP => wpiF' H wp_itree) where
  mono_pred := by
    iintro %Φ %Ψ %HΦ %HΨ #H %pair Hsim; iapply wpiF'_mono
    · iintro !> %t %Φ1; iapply H
    · iexact Hsim
  mono_pred_ne := by
    intro wp Hwp; constructor; intro n ⟨t1, Ψ1⟩ ⟨t2, Ψ2⟩ ⟨Ht, HΨ⟩
    simp at Ht HΨ; subst Ht
    cases h : t1.car.unfold <;> simp [wpiF', wpiF, h]
    case ret r => exact BIFUpdate.ne.ne (HΨ r)
    case tau t' => exact BIFUpdate.ne.ne <| Hwp.ne ⟨rfl, HΨ⟩
    case vis i k =>
      apply BIFUpdate.ne.ne; apply OFE.NonExpansive₂.ne <;> intro a
      · exact Hwp.ne ⟨rfl, HΨ⟩
      · apply BIFUpdate.ne.ne <| Hwp.ne ⟨rfl, λ _ => .rfl⟩

/-- The weakest precondition is defined as the least fixpoint of [wpiF']. -/
def wpi {E R} (H : IHandler (PROP := PROP) E) (t : ITree E R) (Φ : R → PROP) : PROP :=
  bi_least_fixpoint (wpiF' H) (⟨t⟩, Φ)

/-- Unfolding [wpi] reveals one step of the weakest precondition functional. -/
theorem wpi_unfold_emp_mask {R} (t : ITree E R) Φ : wpi H t Φ ⊣⊢ wpiF H (wpi H) t Φ := by
  apply equiv_iff.mp
  apply least_fixpoint_unfold

end wp_itree_def

macro:20 "WPi " t:term:20 " @> " H:term:20 " {{ " Φ:term:20 " }}" : term => `(wpi $H $t $Φ)
macro:20 "WPi " t:term:20 " @> " H:term:20 " {{ " v:ident " , " Q:term:20 " }}" : term => `(wpi $H $t (fun $v => $Q))

delab_rule wpi
  | `($_ $H $t (fun $v:ident => $Q)) => `(WPi $t @> $H {{ $v, $Q }})
  | `($_ $H $t $Φ) => `(WPi $t @> $H {{ $Φ }})

section wp_itree_def

open OFE

variable {E R} {PROP : Type _} [BI PROP] [BIFUpdate PROP]
  (H : IHandler (PROP := PROP) E) (t : ITree E R)

instance : NonExpansive (λ Φ => WPi t @> H {{ Φ }}) := by
  constructor; intro n Φ₁ Φ₂ HΦ
  exact NonExpansive.ne (f := bi_least_fixpoint (wpiF' H)) ⟨rfl, HΦ⟩

theorem wpi_post_congr {Φ Ψ : R → PROP} (HΦ : Φ ≡ Ψ) :
    (WPi t @> H {{ Φ }}) ⊣⊢ (WPi t @> H {{ Ψ }}) :=
  equiv_iff.mp <| NonExpansive.eqv (f := λ Φ => WPi t @> H {{ Φ }}) HΦ

end wp_itree_def

-- Stepping Rules for WPi
section wp_itree_stepping

open ITree BIUpdate OFE

variable {E} {PROP : Type _} [BI PROP] [BIFUpdate PROP] (H : IHandler (PROP := PROP) E)

-- Lean's `rw` does not work with BI equivalences, so we package this update-absorption step as a lemma.
theorem wpi_update_emp_mask {R} (Φ : R → PROP) (t : ITree E R) :
    (|={∅}=> wpi H t Φ) ⊣⊢ wpi H t Φ :=
  equiv_iff.mp <| (BIFUpdate.ne.eqv <| equiv_iff.mpr <| wpi_unfold_emp_mask H t Φ).trans <|
    (equiv_iff.mpr <| fupd_idem).trans <| (equiv_iff.mpr <| wpi_unfold_emp_mask H t Φ).symm

theorem wpi_ret_emp_mask' {R} (Φ : R → PROP) (r : R) :
    (|={∅}=> Φ r) ⊣⊢ (WPi (ret r) @> H {{ Φ }}) :=
  (wpi_unfold_emp_mask H (ret r) Φ).symm

theorem wpi_ret_emp_mask {R} (Φ : R → PROP) (r : R) :
    ⊢ Φ r -∗ (WPi (ret r) @> H {{ Φ }}) := by
  iintro HΦ; iapply (wpi_ret_emp_mask' H Φ r).mp; imodintro; iexact HΦ

theorem wpi_tau_emp_mask {R} (Φ : R → PROP) (t : ITree E R) :
    (WPi (tau t) @> H {{ Φ }}) ⊣⊢ (WPi t @> H {{ Φ }}) :=
  (wpi_unfold_emp_mask H (tau t) Φ).trans <| wpi_update_emp_mask H Φ t

theorem wpi_vis_emp_mask' {R} (Φ : R → PROP) (i : E.I) (k : E.O i → ITree E R) :
    (|={∅}=> H.ihandle i
      (λ a => WPi k a @> H {{ Φ }})
      (λ a => iprop(|={⊤,∅}=> (WPi k a @> H {{ λ _ => iprop(False) }})))) ⊣⊢
    (WPi (vis i k) @> H {{ Φ }}) := by
  refine BiEntails.trans ?_ (wpi_unfold_emp_mask H (vis i k) Φ).symm
  simp [wpiF]

theorem wpi_vis_emp_mask {R} (Φ : R → PROP) (i : E.I) (k : E.O i → ITree E R) :
    H.ihandle i (λ a => WPi k a @> H {{ Φ }})
      (λ a => iprop(|={⊤,∅}=> (WPi k a @> H {{ λ _ => iprop(False) }}))) ⊢
    (WPi (vis i k) @> H {{ Φ }}) := by
  iintro Hwp; iapply (wpi_vis_emp_mask' H Φ i k).mp; imodintro; iexact Hwp

instance uncurry_G_ne {R} (G : ITree E R → (R → PROP) → PROP) :
    (∀ t, NonExpansive (G t)) →
    NonExpansive (λ ((t, Φ) : LeibnizO (ITree E R) × (R → PROP)) => G t.car Φ) := by
  intro Hne; constructor
  intro n ⟨t₁, Φ₁⟩ ⟨t₂, Φ₂⟩ ⟨Ht, HΦ⟩; simp at Ht HΦ
  cases t₁ with | mk t₁ =>
  cases t₂ with | mk t₂ =>
  cases Leibniz.eq_of_eqv (Discrete.discrete Ht)
  exact (Hne t₁).ne HΦ

end wp_itree_stepping

-- Induction principles for WPi
section wp_itree_induction

open ITree BIUpdate OFE

variable {E R} {PROP : Type _} [BI PROP] [BIFUpdate PROP]
  (H : IHandler (PROP := PROP) E) (G : ITree E R → (R → PROP) → PROP)

theorem wpi_ind_emp_mask : (∀ t, NonExpansive (G t)) →
    ⊢ □ (∀ t Φ, wpiF H (λ t' Ψ => iprop(G t' Ψ ∧ (WPi t' @> H {{Ψ}}))) t Φ -∗ G t Φ) -∗
      ∀ t Φ, (WPi t @> H {{ Φ }}) -∗ G t Φ := by
  iintro %Hne #HPre %t %Φ
  let G' : LeibnizO (ITree E R) × (R → PROP) → PROP := λ ⟨t, Φ⟩ => G t.car Φ
  haveI _ := uncurry_G_ne G Hne
  ihave HPre' : □ (∀ y, wpiF' H (λ x => iprop(G' x ∧ bi_least_fixpoint (wpiF' H) x)) y -∗ G' y) $$ []
  · iintro !> %y
    cases y with | mk t' Ψ =>
      simp [G', wpiF', wpi] at ⊢
      iintro Hx
      iapply HPre $$ Hx
  simp [wpi, G'] at ⊢
  iapply (least_fixpoint_ind (wpiF' H) G') $$ HPre' %(⟨t⟩, Φ)

theorem wpi_iter_emp_mask : (∀ t, NonExpansive (G t)) →
    ⊢ □ (∀ t Φ, wpiF H G t Φ -∗ G t Φ) -∗
      ∀ t Φ, (WPi t @> H {{ Φ }}) -∗ G t Φ := by
  iintro %Hne #HPre %t %Φ
  let G' : LeibnizO (ITree E R) × (R → PROP) → PROP := λ ⟨t, Φ⟩ => G t.car Φ
  haveI _ := uncurry_G_ne G Hne
  ihave HPre' : □ (∀ y, wpiF' H G' y -∗ G' y) $$ []
  · iintro !> %y
    cases y with | mk t' Ψ =>
      simp [G', wpiF'] at ⊢
      iintro Hx
      iapply HPre $$ Hx
  simp [wpi, G'] at ⊢
  iapply least_fixpoint_iter <| wpiF' H $$ HPre' %(⟨t⟩, Φ)

theorem wpi_iter_emp_mask' : (∀ t, OFE.NonExpansive (G t)) →
    ⊢ □ (∀ Φ r, (|={∅}=> Φ r) -∗ G (ret r) Φ) -∗
      □ (∀ Φ t, (|={∅}=> G t Φ) -∗ G (tau t) Φ) -∗
      □ (∀ Φ i k, (|={∅}=> H.ihandle i (λ a => G (k a) Φ)
          (λ a => iprop(|={⊤,∅}=> G (k a) (λ _ => iprop(False))))) -∗
        G (vis i k) Φ) -∗
      ∀ t Φ, (WPi t @> H {{ Φ }}) -∗ G t Φ := by
  iintro %Hne #HRet #HTau #HVis; iapply wpi_iter_emp_mask H G Hne;
  iintro !> %t %Φ
  rcases ITree.match_itree t with
    ⟨r, rfl⟩ | ⟨t', rfl⟩ | ⟨i, k, rfl⟩ <;> simp [wpiF] <;> iintro Hwp
  · iapply HRet $$ Hwp
  · iapply HTau $$ Hwp
  · iapply HVis $$ Hwp

end wp_itree_induction

section wp_itree_derived

open ITree OFE

variable {E R} {PROP : Type _} [BI PROP] [BIFUpdate PROP]
  (H : IHandler (PROP := PROP) E) (t : ITree E R)

theorem wpi_upd_wand_emp_mask (Φ Ψ : R → PROP) :
    ⊢ (∀ r, iprop((|={∅}=> Φ r) -∗ (|={∅}=> Ψ r))) -∗
      (WPi t @> H {{ Φ }}) -∗
      (WPi t @> H {{ Ψ }}) := by
  iintro Hwand Hwp
  let G : ITree E R → (R → PROP) → PROP :=
    λ t Φ => iprop(∀ (Ψ : R → PROP), (∀ r, iprop((|={∅}=> Φ r) -∗ (|={∅}=> Ψ r))) -∗ (WPi t @> H {{ Ψ }}))
  iapply wpi_iter_emp_mask' H G $$ [] [] [] [Hwp] [Hwand]
  · -- Prove G t is non-expansive
    intro t; constructor; intro n Φ₁ Φ₂ HΦ; simp [G];
    apply forall_ne; intro Ψ; refine wand_ne.ne ?_ .rfl
    apply forall_ne; intro r
    exact wand_ne.ne (BIFUpdate.ne.ne (HΦ r)) .rfl
  · -- Case ret r
    iintro !> %Φ %r HΦr; simp [G]
    iintro %Ψ Hr; iapply wpi_ret_emp_mask'; iapply Hr $$ HΦr
  · -- Case tau t'
    iintro !> %Φ %t' HG; simp [G]
    iintro %Ψ Hwand; iapply wpi_tau_emp_mask; iapply wpi_update_emp_mask
    imod HG; imodintro; iapply HG $$ %Ψ Hwand
  · -- Case vis i k
    iintro !> %Φ %i %k HG; simp[G]
    iintro %Ψ Hwand; iapply wpi_vis_emp_mask'
    imod HG; imodintro
    iapply H.ihandle_mono i
      (λ a => iprop(∀ Ψ, (∀ r, iprop((|={∅}=> Φ r) -∗ (|={∅}=> Ψ r))) -∗ wpi H (k a) Ψ))
      _ (λ a => iprop(|={⊤,∅}=> G (k a) (λ _ => iprop(False)))) _ $$ [Hwand] [] [HG]
    · iintro %x HG; iapply HG $$ %Ψ Hwand
    · imodintro; iintro %x HG; imod HG; imodintro; iapply HG
      iintro %r Hfalse; iexact Hfalse
    · iexact HG
  · iexact Hwp
  · iexact Hwand

theorem wpi_wand_emp_mask (Φ Ψ : R → PROP) :
    ⊢ (∀ r, iprop(Φ r -∗ Ψ r)) -∗
      (WPi t @> H {{ Φ }}) -∗
      (WPi t @> H {{ Ψ }}) := by
  iintro Hwand Hwp
  iapply wpi_upd_wand_emp_mask H t Φ Ψ $$ [Hwand]
  · iintro %r HΦ; imod HΦ; imodintro; iapply Hwand $$ HΦ
  · iexact Hwp

theorem wpi_update_post_emp_mask :
    (WPi t @> H {{ v, iprop(|={∅}=> Φ v) }}) ⊣⊢
    (WPi t @> H {{ Φ }}) := by
  isplit <;> iintro Hwp
  · iapply wpi_upd_wand_emp_mask H t (λ v => iprop(|={∅}=> Φ v)) Φ
    · iintro %r Hidem; iapply fupd_idem.mp; iexact Hidem
    · iexact Hwp
  · iapply wpi_upd_wand_emp_mask H t Φ <| λ v => iprop(|={∅}=> Φ v)
    · iintro %r HΦr; imodintro; iexact HΦr
    · iexact Hwp

theorem wpi_bind_emp_mask {R T} (t : ITree E T) (k : T → ITree E R) (Φ : R → PROP) :
    ⊢ (WPi t @> H {{ r, WPi (k r) @> H {{ Φ }} }}) -∗
      (WPi (t >>= k) @> H {{ Φ }}) := by
  iintro Hwp
  let G : ITree E T → (T → PROP) → PROP :=
    λ t Φ => iprop(∀ (Ψ : R → PROP) k', (∀ x, Φ x -∗ wpi H (k' x) Ψ) -∗ wpi H (t >>= k') Ψ)
  iapply wpi_iter_emp_mask' H G $$ [] [] [] [Hwp]
  · -- Prove G t is non-expansive
    intro t; constructor; intro n Φ₁ Φ₂ HΦ; simp [G]
    apply forall_ne; intro Ψ; apply forall_ne; intro k'
    refine wand_ne.ne ?_ .rfl
    apply forall_ne; intro x; exact wand_ne.ne (HΦ x) .rfl
  · -- Case ret r
    iintro !> %Φ %r Hwand; simp [G]
    iintro %Ψ %k' HG;
    have hb : ret r >>= k' = k' r := itree_ret_bind r k'; rw [hb];
    iapply wpi_update_emp_mask; imod Hwand; imodintro; iapply HG $$ Hwand
  · -- Case tau t'
    iintro !> %Φ %t' Hwand; simp [G]
    iintro %Ψ %k' Hk; iapply wpi_tau_emp_mask
    iapply wpi_update_emp_mask; imod Hwand; imodintro; iapply Hwand $$ Hk
  · -- Case vis i k
    iintro !> %Φ %i %k Hwand; simp [G]
    iintro %Ψ %k' Hk'; iapply wpi_vis_emp_mask'; imod Hwand; imodintro
    iapply H.ihandle_mono i (λ a => iprop(∀ Ψ k', (∀ x, Φ x -∗ wpi H (k' x) Ψ) -∗ wpi H (k a >>= k') Ψ)) _
      <| λ a => iprop(|={⊤,∅}=> ∀ Ψ k', (∀ x, False -∗ wpi H (k' x) Ψ) -∗ wpi H (k a >>= k') Ψ) $$ [Hk']
    · iintro %a Hwand; iapply Hwand $$ Hk'
    · iintro !> %a Hwand; imod Hwand; imodintro; iapply Hwand;
      iintro %x Hfalse; iexfalso; iexact Hfalse
    · iexact Hwand
  · iexact Hwp
  · iintro %x Hwp; iexact Hwp

end wp_itree_derived

-- Structual rules for WPi
section wp_itree_structural

open ITree BIUpdate OFE

variable {E R} {PROP : Type _} [BI PROP] [BIFUpdate PROP]
  (H : IHandler (PROP := PROP) E) (Φ : R → PROP) (t : ITree E R)

theorem wpi_frame_l_emp_mask (P : PROP) :
    ⊢ P ∗ (WPi t @> H {{ Φ }}) -∗
      (WPi t @> H {{ v, iprop(P ∗ Φ v) }}) := by
  iintro ⟨Hp, Hwp⟩
  iapply wpi_wand_emp_mask H t Φ $$ [Hp]
  · iintro %r Hr; isplitl [Hp]; iexact Hp; iexact Hr
  · iexact Hwp

theorem wpi_frame_r_emp_mask (P : PROP) :
    ⊢ (WPi t @> H {{ Φ }}) ∗ P -∗
      (WPi t @> H {{ v, iprop(Φ v ∗ P) }}) := by
  iintro ⟨Hwp, Hp⟩
  iapply wpi_wand_emp_mask H t Φ $$ [Hp]
  · iintro %r Hr; isplitl [Hr]; iexact Hr; iexact Hp
  · iexact Hwp

end wp_itree_structural
