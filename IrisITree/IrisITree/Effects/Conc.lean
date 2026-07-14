module

import Iris.ProofMode
public import IrisITree.Core.Wpi
public import ITree.Effects.Conc

@[expose] public section

namespace IrisITree.Effects

open Iris Iris.BI ITree ITree.Effects IrisITree.Core

section handler

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]

def concH : IHandler PROP concE where
  ihandle
    | .fork, Φ, Φs => iprop(Φ .parent ∗ |={⊤, ∅}=> Φs .child)
    | .yield, Φ, _ => iprop(|={∅, ⊤}=> |={⊤, ∅}=> Φ ⟨⟩)
    | .kill, _, _ => iprop(|={∅, ⊤}=> True)
  ihandle_mono := by
    iintro %i %Φ %Φ' %Φs %Φs' HΦwand #Hswand HH
    cases i <;> dsimp only
    · icases HH with ⟨HΦ, HΦs⟩
      ihave HΦ' := HΦwand $$ %ForkResult.parent HΦ
      isplitl [HΦ']
      · iexact HΦ'
      · imod HΦs; imodintro; iapply Hswand; iexact HΦs
    · imod HH; itrivial
    · imod HH; imodintro; imod HH; imodintro; iapply HΦwand $$ [$]

end handler

section wpi_rules

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]
  {E : Effect} {H : IHandler PROP E}
  [concE -< E] [Hin : InH concH H]

theorem wpi_kill M (Φ : PUnit → PROP) :
    True -∗ WPi kill @> H; ⊤, M {{Φ}} := by
  iintro Ht; unfold kill
  iapply wpi_trigger_bind
  iapply fupd_mask_intro (by simp); iintro Hm
  simp [concH]; imod Hm; itrivial

theorem wpi_fork M (Φ : PUnit → PROP) :
    Φ ⟨⟩ -∗
    WPi t @> H; ⊤ {{ _v, iprop(True) }} -∗
    WPi fork t @> H; M {{Φ}} := by
  iintro HΦ Ht; unfold fork
  iapply wpi_trigger_bind
  iapply fupd_mask_intro (by simp); iintro Hm
  simp [concH]; isplitl [HΦ Hm];
  · imod Hm; iapply wpi_pure $$ HΦ
  · imod Ht; imodintro; iapply wpi_bind'
    iapply wpi_wand $$ Ht; iintro %_ _
    iapply wpi_kill $$ [$]

theorem wpi_yield (Φ : PUnit → PROP) :
    Φ ⟨⟩ -∗
    WPi yield @> H; ⊤ {{Φ}} := by
  iintro HΦ; unfold yield
  iapply wpi_trigger; simp [concH]
  iapply fupd_mask_intro (by simp); iintro >- !>
  iapply fupd_mask_intro (by simp); iintro >- !>
  iframe

end wpi_rules

section exec

open ITree.Exec IrisITree.Core

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]

instance coneEH_adequate {GE GR} :
    EHandlerAdequate (PROP:=PROP) concH (concEH (GE:=GE) (GR:=GR)) where
  inv s Ms :=
    iprop(<affine> ⌜Ms = s.pool.filterMap λ t =>
      (λ t P => iprop(|={⊤, ∅}=> P t)) <$> t⌝)
  adequate := by
    intro G i s Ms C k Hhandle
    simp [concH, concEH] at Hhandle ⊢
    cases i <;> simp at Hhandle ⊢
    · iintro ⟨_, _⟩ %h !>
      iexists _, _, λ P => P (k .parent),
        Ms ++ [(λ P => iprop(|={⊤, ∅}=> P (k .child)))],
        [λ P => P (k .parent), λ P => iprop(|={⊤, ∅}=> P (k .child))]
      isplitr; itrivial
      isplitr; itrivial
      simp; iframe; isplitr
      · ipureintro; simp [h, ConcState.add]
      · iintro %_ $ //
    · iintro Ht %h !>
      rcases Hhandle with ⟨i, _, _, _, _⟩
      -- iexists _, _, _, _, _
      -- isplitr; ipure_intro; trivial
      sorry
    · iintro Ht %h !>; sorry

end exec
