module

import Iris.ProofMode
public import IrisITree.Core.Wpi
public import ITree.Effects.State

@[expose] public section

namespace IrisITree.Effects

open Iris Iris.BI ITree ITree.Effects IrisITree.Core

section handler

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]

def stateH {S : Type _} (stateInterp : S → PROP) : IHandler PROP (stateE S) where
  ihandle i Φ _ :=
    iprop(∀ s, stateInterp s ={∅}=∗ stateInterp (i s) ∗ Φ s)
  ihandle_mono := by
    iintro %i %Φ %Φ' %s %s' HΦwand #Hswand HH %st Hst
    imod HH $$ Hst with ⟨$, _⟩
    imodintro; iapply HΦwand $$ [$]

instance {S : Type _} (stateInterp : S → PROP) :
    Sequential (stateH stateInterp) := by
  constructor
  iintro %i %Φ %s HH
  simp [stateH]

end handler

section wpi_rules

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP] {S : Type _}
  (stateInterp : S → PROP)
  {E : Effect} {H : IHandler PROP E}
  [stateE S -< E] [Hin : InH (stateH stateInterp) H]

theorem wpi_stateE_get M (Φ : S → PROP) :
    (∀ s, stateInterp s ={M}=∗ stateInterp s ∗ Φ s) -∗
    WPi StateE.get @> H; M {{Φ}} := by
  iintro Hw; unfold StateE.get StateE.modify
  iapply wpi_trigger
  iapply fupd_mask_intro (by simp); iintro Hm
  simp [stateH]; iintro %s Hs; imod Hm
  imod Hw $$ [$] with ⟨$, $⟩
  iapply fupd_mask_intro (by simp); iintro $

theorem wpi_get M (Φ : S → PROP) :
    (∀ s, stateInterp s ={M}=∗ stateInterp s ∗ Φ s) -∗
    WPi get @> H; M {{Φ}} := wpi_stateE_get _ _ _

theorem wpi_stateE_set M s' (Φ : PUnit → PROP) :
    (∀ s, stateInterp s ={M}=∗ stateInterp s' ∗ Φ ⟨⟩) -∗
    WPi StateE.set s' @> H; M {{Φ}} := by
  iintro Hw; unfold StateE.set StateE.modify
  iapply wpi_trigger_bind
  iapply fupd_mask_intro (by simp); iintro Hm
  simp [stateH]; iintro %s Hs; imod Hm
  imod Hw $$ [$] with ⟨$, _⟩
  iapply fupd_mask_intro (by simp); iintro >_
  iapply wpi_pure $$ [$]

theorem wpi_set M s' (Φ : PUnit → PROP) :
    (∀ s, stateInterp s ={M}=∗ stateInterp s' ∗ Φ ⟨⟩) -∗
    WPi set s' @> H; M {{Φ}} := wpi_stateE_set _ _ _ _

end wpi_rules

section exec

open ITree.Exec IrisITree.Core

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]
  {S : Type _} (stateInterp : S → PROP)

instance stateEH_adequate :
    SEHandlerAdequate (stateH stateInterp) (stateEH S) where
  inv s := stateInterp s
  adequate := by
    intro i s C Φ1 Φ2 Hhandle
    simp [stateH, stateEH] at Hhandle ⊢
    iintro Hs Hinv; imod Hs $$ [$] with ⟨_, _⟩
    iintro !>; iexists _, _; iframe
    ipureintro; apply Hhandle

end exec
