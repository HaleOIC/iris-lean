module

public import IrisITree.Core.HandlerAdequate
public import IrisITree.Core.WpiMask
public import ITree

@[expose] public section

namespace IrisITree.Event

open Iris BI ITree Effects

section handler

variable {PROP : Type _} [BI PROP]

def angelicH (α : Type _) : IHandler (PROP := PROP) (angelicE α) where
  ihandle := λ _ Φ _ => iprop(∃ a, Φ a)
  ihandle_mono := by
    iintro %p %Φ %Φ' %s %s' HΦwand #Hswand H
    icases H with ⟨%a, HΦ⟩
    iexists a; iapply HΦwand $$ HΦ

instance angelicH_sequential {α : Type _} :
    Sequential (PROP := PROP) (angelicH (PROP := PROP) α) := by
  constructor
  iintro %p %Φ %s H
  simp [angelicH]

end handler

section wpi_rules

open ITree

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP] {E : Effect}
  {H : IHandler (PROP := PROP) E} {α : Type _}
  [sub : angelicE α -< E] [Hin : InH (angelicH (PROP := PROP) α) H]

theorem wpi_angelic (M : CoPset) (p : α → Prop) (a : {x // p x}) (Ψ : {x // p x} → PROP) :
    Ψ a ⊢ (WPi (choose_angelic p) @> H; M {{ Ψ }}) := by
  change Ψ a ⊢ (WPi trigger (angelicE α) p @> H; M {{ Ψ }})
  iintro HΨ; iapply wpi_trigger (H := H) (angelicH (PROP := PROP) α) M p Ψ
  iapply fupd_mask_intro
  · exact Std.LawfulSet.empty_subset
  · iintro Hfalse; simp [angelicH]; iexists a
    imod Hfalse; imodintro; iexact HΨ

end wpi_rules

section exec

open ITree.Exec IrisITree.Core

instance angelicEH_adequate {PROP : Type _} [BI PROP] [BIFUpdate PROP] {α : Type _} :
    SEHandlerAdequate (angelicH (PROP := PROP) α) (angelicEH α) where
  sehandler_inv _ := iprop(True)
  sehandler_adequate := by
    intro i s C Φ1 Φ2 Hhandle
    simp [angelicH, angelicEH] at Hhandle ⊢
    iintro Hwp Hinv; icases Hwp with ⟨%a, HΦ⟩
    imodintro; iexists a, s
    isplitl []
    · ipure_intro; exact Hhandle a.1 a.2
    · isplitl [Hinv]; iexact Hinv; iexact HΦ

end exec

end IrisITree.Event
