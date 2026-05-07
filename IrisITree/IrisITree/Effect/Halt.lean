module

public import IrisITree.Core.HandlerAdequate
public import IrisITree.Core.Wpi
public import ITree

@[expose] public section

namespace IrisITree.Effect

open Iris BI ITree Effects

section handler

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]

def haltH : IHandler PROP haltE where
  ihandle := λ _ _ _ => iprop(|={∅, ⊤}=> True)
  ihandle_mono := by
    iintro %i %Φ %Φ' %s %s' HΦwand #Hswand HH
    iexact HH

instance haltH_sequential : Sequential (PROP := PROP) haltH := by
  constructor
  iintro %i %Φ %s HH
  simp [haltH]

end handler

section wpi_rules

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]  {E : Effect}
  {H : IHandler PROP E} [sub: haltE -< E] [Hin : InH haltH H]

theorem wpi_halt {R} (Φ : R → PROP) :
    ⊢ (WPi HaltE.halt @> H; ⊤ {{ Φ }}) := by
  unfold HaltE.halt; iapply wpi_bind
  iapply wpi_trigger haltH ⊤ PUnit.unit
  iapply fupd_mask_intro
  · exact Std.LawfulSet.empty_subset
  · iintro Hclose; simp [haltH]; imod Hclose; imodintro; ipure_intro; trivial

theorem wpi_assume [BIAffine PROP] (P : Prop) [Decidable P] (Φ : { _x // P } → PROP) :
    (∀ HP, Φ HP) ⊢ (WPi HaltE.assume P @> H; ⊤ {{ Φ }}) := by
  unfold HaltE.assume; by_cases HP : P <;> (simp [HP]; iintro HΦ)
  · iapply wpi_ret; iapply forall_elim ⟨⟨⟩, HP⟩ $$ HΦ
  · iclear HΦ; iapply wpi_halt

end wpi_rules

section exec

open ITree.Exec ITree.Effects IrisITree.Core

instance haltEH_adequate {PROP : Type _} [BI PROP] [BIFUpdate PROP] :
    SEHandlerAdequate (haltH (PROP := PROP)) haltEH where
  sehandler_inv _ := iprop(True)
  sehandler_adequate := by
    intro i s C Φ1 Φ2 Hhandle
    cases Hhandle

theorem exec_assume {E : Effect} {σ : Type _}
    (P : Prop) [Decidable P] (EH : EHandler E E { _x // P } σ)
    [haltE -< E] [InEH haltEH.toEHandler EH] (s : σ) (C : ITree E { _x // P } → σ → Prop) :
    P → (∀ HP : { _x // P }, C (ITree.ret HP) s) → exec EH (HaltE.assume P) s C := by
  intro hP hC; unfold HaltE.assume
  simp [hP]; apply exec.stop
  exact hC ⟨⟨⟩, hP⟩

end exec

end IrisITree.Effect
