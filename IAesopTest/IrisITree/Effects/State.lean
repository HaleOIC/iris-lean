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
    iaesop bubble
    -- iintro %i %Φ %Φ' %s %s' HΦwand #Hswand HH %st Hst
    -- imod HH $$ Hst with ⟨$, _⟩
    -- imodintro; iapply HΦwand $$ [$]

instance {S : Type _} (stateInterp : S → PROP) :
    Sequential (stateH stateInterp) := by
  constructor
  unfold stateH
  iaesop bubble
  -- iintro %i %Φ %s HH
  -- iexact HH

end handler

section wpi_rules

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP] {S : Type _}
  (stateInterp : S → PROP)
  {E : Effect} {H : IHandler PROP E}
  [stateE S -< E] [Hin : InH (stateH stateInterp) H]

-- Allow a mask-changing fancy update from `Ms` to `Me` while handling `get`.
theorem wpi_stateE_get Ms Me (Φ : S → PROP) :
    (∀ s, stateInterp s ={Ms, Me}=∗ stateInterp s ∗ Φ s) -∗
    WPi StateE.get @> H; Ms, Me {{Φ}} := by
  iintro Hw; unfold StateE.get StateE.modify
  iapply wpi_trigger; simp [stateH]
  iaesop bubble pureBy simp with [backward fupd_mask_intro]
  -- iapply fupd_mask_intro (by simp); iintro Hm
  -- iintro %s Hs; imod Hm
  -- imod Hw $$ [$] with ⟨$, $⟩
  -- iapply fupd_mask_intro (by simp); iintro $

@[iaesop backward 75%]
theorem wpi_get Ms Me (Φ : S → PROP) :
    (∀ s, stateInterp s ={Ms, Me}=∗ stateInterp s ∗ Φ s) -∗
    WPi get @> H; Ms, Me {{Φ}} := wpi_stateE_get _ _ _ _

-- Allow a mask-changing fancy update from `Ms` to `Me` while handling `get`.
theorem wpi_stateE_set Ms Me s' (Φ : PUnit → PROP) :
    (∀ s, stateInterp s ={Ms, Me}=∗ stateInterp s' ∗ Φ ⟨⟩) -∗
    WPi StateE.set s' @> H; Ms, Me {{Φ}} := by
  iintro Hw; unfold StateE.set StateE.modify
  iapply wpi_trigger_bind; simp [stateH];
  iaesop bubble pureBy simp with [backward fupd_mask_intro]
  -- iapply fupd_mask_intro (by simp); iintro Hm
  -- iintro %s Hs; imod Hm
  -- imod Hw $$ [$] with ⟨$, _⟩
  -- iapply fupd_mask_intro (by simp); iintro >_
  -- iapply wpi_pure $$ [$]

@[iaesop backward 75%]
theorem wpi_set Ms Me s' (Φ : PUnit → PROP) :
    (∀ s, stateInterp s ={Ms, Me}=∗ stateInterp s' ∗ Φ ⟨⟩) -∗
    WPi set s' @> H; Ms, Me {{Φ}} := wpi_stateE_set _ _ _ _ _

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
    iaesop bubble pureBy assumption
    -- iintro Hs Hinv; imod Hs $$ [$] with ⟨_, _⟩
    -- iintro !>; iexists _, _; iframe
    -- itrivial

end exec
