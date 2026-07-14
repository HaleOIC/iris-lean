module

import Iris.ProofMode
public import ITree.Effects.Halt
public import IrisITree.Core.Wpi

@[expose] public section

namespace IrisITree.Effects

open Iris Iris.BI ITree IrisITree.Core ITree.Effects

section handler

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]

def haltH : IHandler PROP haltE where
  ihandle := λ _ _ _ => iprop(|={∅, ⊤}=> True)
  ihandle_mono := by
    iintro %i %Φ %Φ' %s %s' HΦwand #Hswand HH
    iexact HH

instance haltH_sequential : Sequential (PROP := PROP) haltH := by
  constructor
  unfold haltH
  iintro %i %Φ %s HH
  iexact HH

end handler

section wpi_rules

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]  {E : Effect}
  {H : IHandler PROP E} [sub: haltE -< E] [Hin : InH haltH H]

theorem wpi_halt {R} (Φ : R → PROP) :
    ⊢ WPi HaltE.halt @> H; ⊤ {{ Φ }} := by
  unfold HaltE.halt; iapply wpi_bind
  iapply wpi_trigger
  iapply fupd_mask_intro
  · exact Std.LawfulSet.empty_subset
  iintro Hclose; simp [haltH]; imod Hclose; itrivial

theorem wpi_assume [BIAffine PROP] (P : Prop) [Decidable P] (Φ : { _x // P } → PROP) :
    (∀ HP, Φ HP) ⊢ WPi HaltE.assume P @> H; ⊤ {{ Φ }} := by
  unfold HaltE.assume; by_cases HP : P <;> (simp [HP]; iintro HΦ)
  · iapply wpi_pure; iapply HΦ
  · iapply wpi_halt

end wpi_rules

section exec

open ITree.Exec ITree.Effects IrisITree.Core

instance haltEH_adequate {PROP : Type _} [BI PROP] [BIFUpdate PROP] :
    SEHandlerAdequate (haltH (PROP := PROP)) haltEH where
  inv _ := iprop(True)
  adequate := by
    intro i s C Φ1 Φ2 Hhandle
    cases Hhandle

end exec
