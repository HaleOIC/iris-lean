module

public import IrisITree.Core.HandlerAdequate
public import IrisITree.Core.WpiMask
public import ITree

@[expose] public section

namespace IrisITree.Effect

open Iris BI ITree Effects

section handler

variable {PROP : Type _} [BI PROP]

def demonicH (α : Type _) : IHandler PROP (demonicE α) where
  ihandle := λ _ Φ _ => iprop(∀ a, Φ a)
  ihandle_mono := by
    iintro %i %Φ %Φ' %s %s' HΦwand #Hswand H %a
    iapply HΦwand; iapply H

instance demonicH_sequential {α : Type _} :
    Sequential (PROP := PROP) (demonicH (PROP := PROP) α) := by
  constructor
  iintro %i %Φ %s H
  simp [demonicH]

end handler

section wpi_rules

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP] {E : Effect}
  {H : IHandler PROP E} {α : Type _}
  [sub : demonicE α -< E] [Hin : InH (demonicH (PROP := PROP) α) H]

theorem wpi_demonic (M : CoPset) (Φ : α → Prop) [Hdec : DecidablePred Φ]
    [Hi: Inhabited {a // Φ a}] (Ψ : {a // Φ a} → PROP) :
    (∀ a, Ψ a) ⊢ (WPi (choose Φ) @> H; M {{ Ψ }}) := by
  change (∀ a, Ψ a) ⊢ (WPi (ITree.trigger (demonicE α) ⟨Φ, Hdec, Hi⟩) @> H; M {{ Ψ }})
  iintro HΨ;
  iapply wpi_trigger (demonicH (PROP := PROP) α) M ⟨Φ, Hdec, Hi⟩ Ψ
  iapply fupd_mask_intro
  · exact Std.LawfulSet.empty_subset
  · iintro Hclose; simp [demonicH]; iintro %a
    imod Hclose; imodintro; iapply HΨ

end wpi_rules

section exec

open ITree.Exec IrisITree.Core

abbrev demonicEH := ITree.Effects.demonicEH
instance demonicEH_adequate {PROP : Type _} [BI PROP] [BIFUpdate PROP] {α : Type _} :
    SEHandlerAdequate (demonicH (PROP := PROP) α) (demonicEH α) where
  sehandler_inv _ := iprop(True)
  sehandler_adequate := by
    intro i s C Φ1 Φ2 Hhandle
    simp [demonicH, demonicEH] at Hhandle ⊢
    rcases Hhandle with ⟨a, s', HC⟩
    iintro HΦ1 Hinv; imodintro
    iexists ⟨a, s'⟩; iexists s
    isplitl []; ipure_intro; exact HC
    isplitl [Hinv]; iexact Hinv
    iapply HΦ1

end exec

end IrisITree.Effect
