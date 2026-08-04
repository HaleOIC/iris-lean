module

public import IrisITree.Core.Handler
public import IrisITree.Core.Wpi
public import Iris.ProofMode
public import Iris.BI.Lib.Fixpoint
public import Iris.BI.BigOp.BigSepList
public import ITree.Definition
public import ITree.Exec

@[expose] public section

namespace IrisITree.Core

open Iris BI ITree Std OFE

def bi_close {PROP : Type _} [BI PROP] {α : Type _} (R : α → α → Prop) (P : α → PROP) : α → PROP :=
  λ a => iprop(∃ a', ⌜R a a'⌝ ∗ P a')

section bi_close

variable {PROP : Type _} [BI PROP] [BIAffine PROP] {α : Type} (R : α → α → Prop)

theorem bi_close_mono (P1 P2 : α → PROP) (a : α) :
    bi_close R P1 a ⊢ (∀ y, P1 y -∗ P2 y) -∗ bi_close R P2 a := by
  simp [bi_close]
  iaesop bubble
  -- iintro Hclose Hwand;
  -- icases Hclose with ⟨%a', %HR, HP1⟩
  -- iexists a'; isplitr
  -- · ipureintro; exact HR
  -- · iapply Hwand $$ HP1

theorem bi_close_intro (P : α → PROP) (a : α) [Href : Reflexive R] :
    P a ⊢ bi_close R P a := by
  simp [bi_close]
  iaesop bubble pureBy exact Href.refl
  -- iintro HP
  -- iexists a; isplitr
  -- · ipureintro; exact Href.refl
  -- · iexact HP

theorem bi_close_respect (P : α → PROP) [Hsym : Symm R] [Htran : Trans R R R] :
    ∀ {x y : α}, R x y → bi_close R P x ⊣⊢ bi_close R P y := by
  simp only [bi_close]
  iaesop bubble pureStop
  · exact Htran.trans (Hsym.symm _ _ h0_1) H1_5
  · exact Htran.trans h0_1 H1_5
  -- intro x y Hxy
  -- isplit <;> (
  --   iintro Hclose; simp [bi_close]; icases Hclose with ⟨%a', %Hra, HP⟩;
  --   iexists a'; isplitr; ipureintro
  -- )
  -- · exact Htran.trans (Hsym.symm x y Hxy) Hra
  -- · iexact HP
  -- · exact Htran.trans Hxy Hra
  -- · iexact HP

end bi_close

/-- [bi_mono0] : linear monotone closure of a predicate transformer. -/
def bi_mono0 {PROP : Type _} [BI PROP] {α : Type _} (P : (α → PROP) → PROP) : (α → PROP) → PROP :=
  λ Q => iprop(∃ Q' : α → PROP, P Q' ∗ ∀ x, Q' x -∗ Q x)

section bi_mono0

variable {PROP : Type _} [BI PROP] {α : Type _}

theorem bi_mono0_intro0 (P : (α → PROP) → PROP) (Q : α → PROP) :
    P Q ⊢ bi_mono0 P Q := by
  simp only [bi_mono0]
  iaesop bubble
  -- iintro HP
  -- iexists Q; isplitl [HP]
  -- · iexact HP
  -- · iintro %x HQ; iexact HQ

@[iaesop backward 70%]
theorem bi_mono0_mono (P : (α → PROP) → PROP) (Q1 Q2 : α → PROP) :
    bi_mono0 P Q1 ⊢ (∀ x, Q1 x -∗ Q2 x) -∗ bi_mono0 P Q2 := by
  simp only [bi_mono0]
  iaesop bubble
  -- iintro Hm HQ
  -- icases Hm with ⟨%Q', HP, HQ1⟩
  -- iexists Q'; isplitl [HP]
  -- · iexact HP
  -- · iintro %x HQ'; iapply HQ; iapply HQ1; iapply HQ'

theorem bi_mono0_mono_l (P1 P2 : (α → PROP) → PROP) (Q : α → PROP) :
    bi_mono0 P1 Q ⊢ (∀ Q, P1 Q -∗ P2 Q) -∗ bi_mono0 P2 Q := by
  simp only [bi_mono0]
  iaesop bubble
  -- iintro Hm HP
  -- icases Hm with ⟨%Q', HP1, HQ1⟩
  -- iexists Q'; isplitl [HP HP1]
  -- · iapply HP $$ %Q' HP1
  -- · iexact HQ1

theorem bi_mono0_elim (P : (α → PROP) → PROP) (Q : α → PROP) :
    bi_mono0 P Q ⊢ (∀ Q Q', (∀ x, Q' x -∗ Q x) -∗ P Q' -∗ P Q) -∗ P Q := by
  simp only [bi_mono0]
  iaesop bubble
  -- iintro Hm HP;
  -- icases Hm with ⟨%Q', HPQ', HQ1⟩
  -- iapply HP $$ %Q %Q' HQ1 HPQ'

theorem bi_mono0_dup (P : (α → PROP) → PROP) (Q : α → PROP) :
    bi_mono0 (bi_mono0 P) Q ⊢ bi_mono0 P Q := by
  simp only [bi_mono0]
  iaesop bubble
  -- iintro H
  -- icases H with ⟨%Q', Houter, HQw⟩
  -- icases Houter with ⟨%Q'', HP, HQw'⟩
  -- iexists Q''; isplitl [HP]
  -- · iexact HP
  -- · iintro %x HQ''; iapply HQw; iapply HQw' $$ HQ''

theorem bi_mono0_intro (P : (α → PROP) → PROP) (Q Q' : α → PROP) :
    P Q' ⊢ (∀ x, Q' x -∗ Q x) -∗ bi_mono0 P Q := by
  simp only [bi_mono0]
  iaesop bubble
  -- iintro HP HQ
  -- iexists Q'; isplitl [HP]
  -- · iexact HP
  -- · iexact HQ

end bi_mono0

/-- The functional whose least fixed point is `lfp_tp`. -/
def lfp_tpF {PROP : Type _} [BI PROP] {α : Type _}
    (F : (α → PROP) → (α → PROP))
    (rec_tp : DiscreteO (List ((α → PROP) → PROP)) → PROP) :
    DiscreteO (List ((α → PROP) → PROP)) → PROP :=
  λ Ms => iprop(
    ∀ (i : Nat) (M : (α → PROP) → PROP), ⌜Ms.car[i]? = some M⌝ -∗
      bi_mono0 M λ x => iprop(
        ∃ G, F G x ∗ ∀ Ms', ([∗list] M' ∈ Ms', M' G) -∗ rec_tp ⟨Ms' ++ Ms.car.eraseIdx i⟩
      )
  )

section lfp_tp

variable {PROP : Type _} [BI PROP] [BIAffine PROP] {α : Type _}
  (F : (α → PROP) → (α → PROP))

instance lfp_tpF_ne : NonExpansive (lfp_tpF F) where
  ne {_ _ _} Hfg := by
    intro Ms; unfold lfp_tpF bi_mono0
    refine forall_ne λ i => forall_ne λ _ => ?_
    refine wand_ne.ne .rfl $ exists_ne λ _ => ?_
    refine sep_ne.ne .rfl $ forall_ne λ _ => ?_
    refine wand_ne.ne .rfl $ exists_ne λ _ => ?_
    refine sep_ne.ne .rfl $ forall_ne λ Ms' => ?_
    exact wand_ne.ne .rfl $ Hfg ⟨Ms' ++ Ms.car.eraseIdx i⟩

@[iaesop backward 70%]
theorem lfp_tpF_mono (tp1 tp2 : DiscreteO (List ((α → PROP) → PROP)) → PROP) :
    ⊢ □ (∀ Ms, tp1 Ms -∗ tp2 Ms) -∗
      ∀ Ms, lfp_tpF F tp1 Ms -∗ lfp_tpF F tp2 Ms := by
  iintro #Hwand %Ms Htp; unfold lfp_tpF
  iintro %i %M %Hi
  ispecialize Htp $$ %i %M %Hi
  iaesop bubble
  -- iapply bi_mono0_mono $$ Htp
  -- iintro %x ⟨%G, HF, HMS⟩; iexists G; isplitl [HF]
  -- · iexact HF
  -- · iintro %Ms HM'; iapply Hwand; iapply HMS $$ HM'

instance : BIMonoPred (lfp_tpF (PROP := PROP) F) where
  mono_pred := by
    iaesop bubble
    -- iintro %Φ %Ψ %HneΦ %HneΨ #Hwand %Ms HΦ
    -- iapply lfp_tpF_mono F Φ Ψ $$ [] [HΦ] <;> iaesop
    -- · iexact Hwand
    -- · iexact HΦ
  mono_pred_ne.ne n Φ Φ' Hdist := by
    cases Hdist; rfl

end lfp_tp

/-- The `lfp_tp` least-fixed-point predicate. -/
def lfp_tp {PROP : Type _} [BI PROP] {α : Type _}
    (F : (α → PROP) → (α → PROP))
    (Ms : List ((α → PROP) → PROP)) : PROP :=
  bi_least_fixpoint (lfp_tpF F) ⟨Ms⟩

section lfp_tp_lemmas

variable {PROP : Type _} [BI PROP] [BIAffine PROP] {α : Type _}
  (F : (α → PROP) → (α → PROP))

@[iaesop backward 75%]
theorem lfp_tp_unfold (Ms : List ((α → PROP) → PROP)) :
    lfp_tp F Ms ⊣⊢ lfp_tpF F (λ Ms => lfp_tp F Ms.car) ⟨Ms⟩ :=
  equiv_iff.mp <| least_fixpoint_unfold (lfp_tpF F)

@[iaesop backward 70%]
theorem lfp_tp_nil : ⊢ (lfp_tp F [] : PROP) := by
  iapply (lfp_tp_unfold F []).mpr
  simp only [lfp_tpF]
  iintro %i %M %Hi; simp at Hi

theorem lfp_tp_ind (Φ : DiscreteO (List ((α → PROP) → PROP)) → PROP)
    [NonExpansive Φ] :
    ⊢ □ (∀ y, lfp_tpF F (λ x => iprop(Φ x ∧ lfp_tp F x.car)) y -∗ Φ y) -∗
      (∀ Ms, lfp_tp F Ms.car -∗ Φ Ms) := by
  iintro #Hwand %Ms Hlfp
  iapply least_fixpoint_ind (lfp_tpF (PROP := PROP) F)
  · iaesop bubble pureBy simp [lfp_tp] with [backward BI.and_congr_right]
    -- iintro !> %y Hlfp; iapply Hwand;
    -- iapply lfp_tpF_mono F $$ [] Hlfp
    -- iintro !> %Ms Hpre; iapply BI.and_congr_right $$ Hpre
    -- simp [lfp_tp]
  · simp [lfp_tp]; iaesop bubble

-- Helper function for [lfp_*_perm_*]
theorem perm_pick_erase {β : Type _} {Ms1 Ms2 : List β} {i : Nat} {M : β}
    (hperm : Ms1.Perm Ms2) (Hi : Ms2[i]? = some M) :
    ∃ j, Ms1[j]? = some M ∧ (Ms1.eraseIdx j).Perm (Ms2.eraseIdx i) := by
  induction hperm generalizing i M with
  | nil => simp at Hi
  | cons x hperm ih => cases i with
    | zero => simp at Hi; subst M; refine ⟨0, ?_, ?_⟩; simp; simpa
    | succ i =>
      simp at Hi; rcases ih Hi with ⟨j, Hj, Hperm⟩
      refine ⟨j + 1, ?_, ?_⟩
      · simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using Hj
      · simpa [List.eraseIdx_cons_succ] using List.Perm.cons x Hperm
  | swap x y l => cases i with
    | zero => simp at Hi; subst M; refine ⟨1, ?_, ?_⟩; simp; simp
    | succ i => cases i with
      | zero => simp at Hi; subst M; refine ⟨0, ?_, ?_⟩; simp; simp
      | succ i =>
        simp at Hi; refine ⟨i + 2, ?_, ?_⟩
        · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Hi
        · simpa [List.eraseIdx, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using List.Perm.swap x y (l.eraseIdx i)
  | trans h₁ h₂ ih₁ ih₂ =>
      rcases ih₂ Hi with ⟨j₂, Hj₂, Hperm₂⟩
      rcases ih₁ Hj₂ with ⟨j₁, Hj₁, Hperm₁⟩
      exact ⟨j₁, Hj₁, List.Perm.trans Hperm₁ Hperm₂⟩

@[iaesop backward 75%]
theorem lfp_tpF_perm (Ms1 Ms2 : List ((α → PROP) → PROP))
    (wp1 wp2 : DiscreteO (List ((α → PROP) → PROP)) → PROP)
    (h : Ms1.Perm Ms2) :
    lfp_tpF F wp1 ⟨Ms1⟩ ⊢
    (∀ (Ns1 Ns2 : DiscreteO (List ((α → PROP) → PROP))),
      ⌜Ns1.car.Perm Ns2.car⌝ -∗ wp1 Ns1 -∗ wp2 Ns2) -∗
    lfp_tpF F wp2 ⟨Ms2⟩ := by
  iintro Htp Hwp; unfold lfp_tpF; iintro %i %M %Hi
  rcases perm_pick_erase h Hi with ⟨j, Hj, Herase⟩
  ispecialize Htp $$ %j %M %Hj
  iaesop bubble pureStop
  exact (List.perm_append_left_iff Ms').2 Herase
  -- iapply bi_mono0_mono $$ Htp
  -- iintro %x Hstep; icases Hstep with ⟨%G, HFx, Hcont⟩
  -- iexists G; isplitl [HFx]; iexact HFx
  -- iintro %Ms' HM';
  -- iapply Hwp $$ %⟨Ms' ++ Ms1.eraseIdx j⟩ %⟨Ms' ++ Ms2.eraseIdx i⟩
  -- · ipureintro; simp; exact (List.perm_append_left_iff Ms').2 Herase
  -- · iapply Hcont $$ HM'

theorem lfp_tpF_perm_close (Ms1 Ms2 : List ((α → PROP) → PROP))
    (wp : DiscreteO (List ((α → PROP) → PROP)) → PROP)
    (h : Ms1.Perm Ms2) :
    lfp_tpF F wp ⟨Ms1⟩ ⊢
    lfp_tpF F (bi_close (λ a b => a.car.Perm b.car) wp) ⟨Ms2⟩ := by
  iintro Htp; iapply lfp_tpF_perm $$ Htp
  · exact h
  · simp only [bi_close]
    iaesop bubble pureStop
    exact h0_1.symm
    -- iintro %Ns1 %Ns2 %Hperm Hwp;
    -- iexists Ns1; isplitr
    -- · ipureintro; exact Hperm.symm
    -- · iexact Hwp

@[iaesop backward 50%]
theorem lfp_tp_perm (Ms1 Ms2 : List ((α → PROP) → PROP)) (h : Ms1.Perm Ms2) :
    ⊢ lfp_tp F Ms1 -∗ lfp_tp F Ms2 := by
  letI : NonExpansive λ (Ms : DiscreteO (List ((α → PROP) → PROP))) =>
    iprop(∀ Ms2, ⌜Ms.car.Perm Ms2⌝ -∗ lfp_tp F Ms2) := ⟨
      λ n lst1 lst2 Hlst => by
        refine forall_ne (λ lst => ?_)
        cases Hlst; rfl
    ⟩
  iintro Htp; irevert %Ms2 %h
  iapply lfp_tp_ind F λ Ms => iprop(∀ Ms2, ⌜Ms.car.Perm Ms2⌝ -∗ lfp_tp F Ms2) $$ [] Htp
  iaesop bubble with [backward lfp_tpF_perm, backward lfp_tp_unfold]
  -- iintro !> %Ms1 Htp %Ms2 %Hperm;
  -- iapply lfp_tp_unfold
  -- iapply lfp_tpF_perm F Ms1.car _ _ _ Hperm $$ Htp
  -- iintro %Ns1 %Ns2 %Hperm Hw; icases Hw with ⟨H, -⟩
  -- iapply H; ipureintro; exact Hperm

theorem lfp_tp_app (Ms1 Ms2 : List ((α → PROP) → PROP)) :
    ⊢ lfp_tp F Ms1 -∗ lfp_tp F Ms2 -∗ lfp_tp F (Ms1 ++ Ms2) := by
  letI : NonExpansive λ (Ms : DiscreteO (List ((α → PROP) → PROP))) =>
    iprop(∀ Ms2, lfp_tp F Ms2 -∗ lfp_tp F (Ms.car ++ Ms2)) := ⟨
      λ n ls1 lst2 Hlst => by
        refine forall_ne (λ Ms2 => ?_)
        cases Hlst; rfl
    ⟩
  letI : NonExpansive λ (Ms : DiscreteO (List ((α → PROP) → PROP))) =>
    iprop(∀ Ms1, lfp_tpF F (λ x => iprop((∀ Ms, lfp_tp F Ms -∗ lfp_tp F (x.car ++ Ms))
      ∧ lfp_tp F x.car)) Ms1 -∗ lfp_tp F (Ms1.car ++ Ms.car)) := ⟨
        λ n lst1 lst2 Hlst => by
          refine forall_ne (λ Ms1 => ?_)
          cases Hlst; rfl
      ⟩
  -- TODO: Try to remove these two have statements
  have Hwrap : ⊢ (∀ (Ms1 : DiscreteO (List ((α → PROP) → PROP))),
    iprop(lfp_tp F Ms1.car -∗ ∀ Ms2, iprop(lfp_tp F Ms2 -∗
      lfp_tp F (Ms1.car ++ Ms2)))) -∗
    ∀ (Ms1 : List ((α → PROP) → PROP)), iprop(lfp_tp F Ms1 -∗
      ∀ Ms2, iprop(lfp_tp F Ms2 -∗ lfp_tp F (Ms1 ++ Ms2))) := by
    iintro H %Ms1 Hx1 %Ms2 Hx2
    iapply H $$ %⟨Ms1⟩ Hx1 %Ms2 Hx2
  have Hwrap2 : ⊢ (∀ (Ms2 : DiscreteO (List ((α → PROP) → PROP))),
    iprop(lfp_tp F Ms2.car -∗ ∀ Ms1, iprop(lfp_tpF F (λ x =>
      iprop((∀ Ms, lfp_tp F Ms -∗ lfp_tp F (x.car ++ Ms)) ∧ lfp_tp F x.car)) Ms1 -∗
      lfp_tp F (Ms1.car ++ Ms2.car)))) -∗
    ∀ (Ms2 : List ((α → PROP) → PROP)), iprop(lfp_tp F Ms2 -∗ BI.forall (λ Ms1 =>
      iprop(lfp_tpF F (λ x => iprop((∀ Ms, lfp_tp F Ms -∗ lfp_tp F (x.car ++ Ms)) ∧
      lfp_tp F x.car)) Ms1 -∗ lfp_tp F (Ms1.car ++ Ms2)))) := by
    iintro H %Ms2 Hx2 %Ms1 Hx1
    iapply H $$ %⟨Ms2⟩ Hx2 %Ms1 Hx1
  iintro Hx1 Hx2; irevert %Ms1 Hx1 %Ms2 Hx2; iapply Hwrap; iclear %Hwrap
  iapply lfp_tp_ind F λ Ms => iprop(∀ Ms2, lfp_tp F Ms2 -∗ lfp_tp F (Ms.car ++ Ms2))
  iintro !> %Ms1 Hx1 %Ms2 Hx2; irevert %Ms2 Hx2 %Ms1 Hx1; iapply Hwrap2; iclear %Hwrap2
  iapply lfp_tp_ind F λ Ms => iprop(∀ Ms1, lfp_tpF F (λ x =>
    iprop((∀ Ms, lfp_tp F Ms -∗ lfp_tp F (x.car ++ Ms)) ∧ lfp_tp F x.car)) Ms1 -∗
      lfp_tp F (Ms1.car ++ Ms.car))
  repeat clear this
  iintro !> %Ms2 Hx2 %Ms1 Hx1; iapply lfp_tp_unfold; unfold lfp_tpF at ⊢; simp
  iintro %i %M %Hlookup
  by_cases Hi : i < Ms1.car.length
  · -- M appears in Ms1
    have Hloc := List.getElem?_append_left Hi ▸ Hlookup
    rw [List.eraseIdx_append_of_lt_length Hi Ms2.car]
    ispecialize Hx1 $$ %i %M %Hloc; iapply bi_mono0_mono $$ Hx1
    iintro %x ⟨%G, ⟨HF, Hcont⟩⟩
    iexists G; iframe
    iintro %Ms' HMs'; ispecialize Hcont $$ %Ms' HMs'
    icases Hcont with ⟨Happend, -⟩; iapply Happend
    iapply (lfp_tp_unfold F Ms2.car).mpr; simp only [lfp_tpF]
    iintro %j %N %Hj; ispecialize Hx2 $$ %j %N %Hj
    iapply bi_mono0_mono $$ Hx2
    iintro %x ⟨%G, ⟨HF, Hcont⟩⟩; iexists G; iframe
    iintro %Ms' HMs'; ispecialize Hcont $$ %Ms' HMs'
    iaesop bubble
    -- iapply Hcont
  · -- M appears in Ms2
    have Hi := Nat.le_of_not_gt Hi
    have Hloc := List.getElem?_append_right Hi ▸ Hlookup
    rw [List.eraseIdx_append_of_length_le Hi Ms2.car]
    ispecialize Hx2 $$ %(i - Ms1.car.length) %M %Hloc
    iapply bi_mono0_mono $$ Hx2
    iintro %x ⟨%G, ⟨HF, Hcont⟩⟩; iexists G; iframe
    iintro %Ms' HMs'; ispecialize Hcont $$ %Ms' HMs'
    icases Hcont with ⟨Happend, -⟩
    iaesop bubble pureStop
    -- ispecialize Happend $$ %Ms1 Hx1
    -- iapply lfp_tp_perm F $$ [$]
    rfl
    apply List.perm_append_comm_assoc

@[iaesop backward 75%]
theorem lfp_tp_cons (M : (α → PROP) → PROP) (Ms : List ((α → PROP) → PROP)) :
    ⊢ lfp_tp F [M] -∗ lfp_tp F Ms -∗ lfp_tp F (M :: Ms) := by
  simpa using (lfp_tp_app F [M] Ms)

@[iaesop backward 75%]
theorem lfp_tp_singleton_mod_elim (M : (α → PROP) → PROP) :
    ⊢ M (λ x => lfp_tp F [λ P => P x]) -∗ lfp_tp F [M] := by
  iintro Hx; iapply lfp_tp_unfold; simp only [lfp_tpF]
  iintro %i %M' %Hi; cases i with
  | zero =>
    simp at Hi; subst M'; simp only [List.eraseIdx, List.append_nil]
    iapply bi_mono0_intro M $$ Hx; iintro %x Hlfp;
    ihave Hlfp := lfp_tp_unfold F [λ P => P x] $$ Hlfp; simp only [lfp_tpF];
    have Hlookup : ([λ P => P x] : List ((α → PROP) → PROP))[0]? = some (λ P => P x) := by simp
    ispecialize Hlfp $$ %0 %(λ P => P x) %Hlookup
    simp only [List.eraseIdx, List.append_nil]
    iapply bi_mono0_elim $$ Hlfp;
    iaesop bubble
    -- iintro %Q %Q' Hwand HQ'
    -- iapply Hwand $$ HQ'
  | succ n => simp at Hi

variable {α : Type _} [OFE α] [OFE.Discrete α]

-- TODO: replace the lean' induction with native tactic `iinduction`
theorem lfp_tp_intro (G : (α → PROP) → (α → PROP)) (x : α) :
    ⊢ bi_least_fixpoint G x -∗ lfp_tp G [λ P => P x] := by
  letI : NonExpansive (fun (x : α) => lfp_tp G [λ P => P x] : α → PROP) := ⟨
    fun {n x1 x2} Hx => by
      have Heq : x1 = x2 := (OFE.Discrete.discrete Hx).to_eq
      subst Heq; rfl
  ⟩

  have Hlist : ∀ Ms : List ((α → PROP) → PROP),
      ⊢ ([∗list] M ∈ Ms, M (λ x => lfp_tp G [λ P => P x])) -∗ lfp_tp G Ms := by
    intro Ms
    induction Ms with
    | nil =>
      iaesop bubble
      -- iintro -; iapply lfp_tp_nil
    | cons M Ms ih =>
      iintro HMs
      ihave HMs := BigSepL.bigSepL_cons.mp $$ HMs
      iaesop bubble
      -- icases HMs with ⟨HM, HMs⟩
      -- ihave HM := lfp_tp_singleton_mod_elim G M $$ HM
      -- iapply lfp_tp_cons G M Ms $$ HM
      -- iapply ih $$ HMs
  iintro Hlfp; irevert %x Hlfp
  iapply least_fixpoint_iter
  clear this
  iintro !> %x HF; iapply lfp_tp_unfold
  simp only [lfp_tpF]
  iintro %i %M %Hi
  cases i with
  | zero =>
    simp at Hi; subst M
    simp only [List.eraseIdx, List.append_nil]
    iapply bi_mono0_intro0; simp only []
    iexists _; isplitl [HF]
    · iassumption
    · iintro %Ms HMs; istop
      induction Ms with
      | nil => iintro HMs; iapply lfp_tp_nil
      | cons M Ms IHM =>
        iintro HMs
        ihave HMs := BigSepL.bigSepL_cons $$ HMs
        iaesop bubble
        -- icases HMs with ⟨HM, HMs⟩
        -- ihave HM := lfp_tp_singleton_mod_elim G M $$ HM
        -- iapply lfp_tp_cons G M Ms $$ HM
        -- iapply IHM $$ [$]
  | succ i => simp at Hi

end lfp_tp_lemmas

end IrisITree.Core
