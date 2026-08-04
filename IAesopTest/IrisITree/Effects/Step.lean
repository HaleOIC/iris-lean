module

import Iris.ProofMode
public import IrisITree.Core.Wpi
public import ITree.Effects.Step
public import Iris.Instances.Lib.FUpd

@[expose] public section

namespace IrisITree.Effects

open Iris Iris.BI ITree ITree.Effects IrisITree.Core

section handler

variable {PROP : Type _} [BI PROP]

/-- A logical modality used to interpret operational `step` events. -/
class StepMod (PROP : Type _) [BI PROP] where
  apply : PROP → PROP
  mono (P Q : PROP) : ⊢@{PROP} (P -∗ Q) -∗ apply P -∗ apply Q

instance : CoeFun (StepMod PROP) (λ _ => PROP → PROP) where
  coe m := @StepMod.apply PROP _ m

namespace StepMod

-- [Warning] unrestricted recursive backward rule
theorem map (m : StepMod PROP) (P Q : PROP) :
    ⊢@{PROP} m P -∗ (P -∗ Q) -∗ m Q := by
  iaesop bubble with [backward StepMod.mono]
  -- iintro HP Hwand
  -- iapply (@StepMod.mono PROP _ m P Q) $$ Hwand HP

/-- Interpret a step without adding a logical modality. -/
@[reducible] def ident : StepMod PROP where
  apply P := P
  mono _ _ := by
    iaesop bubble
    -- iintro Hwand HP
    -- iapply Hwand $$ [$]

/-- Interpret a step as one logical later. -/
@[reducible] def later : StepMod PROP where
  apply P := iprop(▷ P)
  mono _ _ := by
    iaesop bubble
    -- iintro Hwand HP
    -- inext; iapply Hwand $$ [$]

theorem wand (m : StepMod PROP) (P Q : PROP) :
    ⊢@{PROP} m iprop(P -∗ Q) -∗ P -∗ m Q := by
  iintro Hwand HP
  iapply m.map $$ Hwand
  iaesop bubble
  -- iintro HPQ
  -- iapply HPQ $$ HP

end StepMod

/-- Interpret an operational step using `m`. -/
def stepH (m : StepMod PROP) : IHandler PROP stepE where
  ihandle := λ _ Φ _ => m (Φ ⟨⟩)
  ihandle_mono := by
    iintro %_ %Φ %Φ' %_ %_ HΦwand _ HΦ
    ispecialize HΦwand $$ %⟨⟩
    iapply m.map $$ HΦ HΦwand

instance stepH_sequential (m : StepMod PROP) : Sequential (stepH m) := by
  constructor
  simp only [stepH]
  iaesop bubble
  -- iintro %_ %_ %_ H
  -- iexact H

/-- An identity step interpretation implies a later step interpretation. -/
instance stepH_ident_later :
    WandH (stepH .ident (PROP := PROP)) (stepH .later) := by
  constructor
  intro _ _ _
  exact entails_wand later_intro

end handler

section wpi_rules

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]
  {E : Effect} {H : IHandler PROP E}
  {m : StepMod PROP}
  [sub : stepE -< E] [Hin : InH (stepH m) H]

@[iaesop backward 75%]
theorem wpi_step M (Φ : PUnit → PROP) :
    m iprop(|={M}=> Φ ⟨⟩) -∗
    WPi step @> H; M {{ Φ }} := by
  change m iprop(|={M}=> Φ ⟨⟩) -∗
    WPi (@Effect.trigger stepE E sub ⟨⟩) @> H; M {{ Φ }}
  iintro HΦ; iapply wpi_trigger; simp only [stepH]
  iaesop bubble simp pureBy simp
    with [backward StepMod.map 10%, backward fupd_mask_intro]
  -- iapply fupd_mask_intro (by simp)
  -- iintro Hclose; iapply m.map $$ HΦ
  -- iintro HΦ; imod Hclose; imod HΦ
  -- imodintro; iframe

end wpi_rules

section exec

open ITree.Exec

variable {GF : BundledGFunctors} [InvGS GF]

/-- Executing an identity-interpreted step requires no later credits. -/
instance stepEH_ident_adequate :
    SEHandlerAdequate (stepH (.ident (PROP := IProp GF))) (stepEH (λ _ => 0)) where
  inv _ := iprop(True)
  adequate := by
    intro i s C Φ₁ Φ₂ Hhandle
    simp only [stepH, stepEH] at *
    simp only [Nat.zero_le, true_and, Nat.sub_zero] at Hhandle
    iaesop bubble simp
    -- iintro HΦ _ !>
    -- iexists ⟨⟩, (ULift.up (s.1.down + 1), ULift.up s.2.down)
    -- iframe; itrivial

/-- Executing a later-interpreted step consumes one later credit. -/
instance stepEH_later_adequate :
    SEHandlerAdequate (stepH (.later (PROP := IProp GF))) (stepEH (λ _ => 1)) where
  inv s := £ s.2.down
  adequate := by
    intro i s C Φ₁ Φ₂ Hhandle
    simp only [stepH, stepEH] at *
    obtain ⟨Hcredit, HC⟩ := Hhandle
    iintro HΦ Hlc
    ihave Hparts : £ 1 ∗ £ (s.2.down - 1) $$ [Hlc]
    · iapply lc_split.mp
      rw [Nat.add_sub_of_le Hcredit]
      iexact Hlc
    icases Hparts with ⟨Hone, Hrest⟩
    imod lc_fupd_elim_later $$ Hone HΦ with HΦ
    iaesop bubble simp
    -- imodintro
    -- iexists ⟨⟩, (ULift.up (s.1.down + 1), ULift.up (s.2.down - 1))
    -- iframe; itrivial

end exec
