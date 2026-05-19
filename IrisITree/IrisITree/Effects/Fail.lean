module

import Iris.ProofMode
public import ITree.Effects.Fail
public import IrisITree.Core.Wpi

@[expose] public section

namespace IrisITree.Effects

open Iris Iris.BI ITree IrisITree.Core ITree.Effects

section handler

variable {PROP : Type _} [BI PROP]

def failH : IHandler PROP failE where
  ihandle := λ _ _ _ => iprop(False)
  ihandle_mono := by
    iintro %i %Φ %Φ' %s %s' HΦwand #Hswand HH
    icases HH with ⟨⟩

instance failH_sequential : Sequential (PROP := PROP) failH := by
  constructor
  iintro %i %Φ %s Hwand
  icases Hwand with ⟨⟩

end handler

section wpi_rules

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP] {E : Effect}
  {H : IHandler PROP E} [sub : failE -< E] [Hin : InH failH H]

theorem wpi_fail {R} (M : CoPset) (Φ : R → PROP) (s : String) :
    (WPi fail s @> H; M {{ Φ }}) ⊢ |={M}=> iprop(False) := by
  iintro Hwp; simp [fail, Effect.trigger]
  sorry
  -- ihave >Hwp := wpi_trigger $$ Hwp
  -- simp [IHandler.ihandle]
  -- have key : ∀ (Ψ₁ Ψ₂ : failE.O ({ down := s } : failE.I) → PROP),
  --     H.ihandle (@Subeffect.map failE E sub ({ down := s } : failE.I)).fst
  --       (fun a => Ψ₁ ((@Subeffect.map failE E sub ({ down := s } : failE.I)).snd a))
  --       (fun a => Ψ₂ ((@Subeffect.map failE E sub ({ down := s } : failE.I)).snd a)) ⊢
  --       iprop(False) := by
  --   intro Ψ₁ Ψ₂
  --   refine (Hin.is_inH ({ down := s } : failE.I) Ψ₁ Ψ₂).mpr.trans ?_
  --   exact false_elim
  -- -- iapply ((key (fun p => wpi (H := H) (R := R) ∅ (nomatch p)
  --     -- (fun v => iprop(|={∅,M}=> Φ v)))
  --   -- (fun p => wpi (H := H) (R := R) ⊤ (nomatch p)
  --     -- (fun _ => iprop(False)))).trans false_elim)
  -- sorry
  -- -- iexact Hwp

omit Hin in
theorem wpi_assert {M} (P : Prop) [Decidable P] (Φ : PUnit → PROP) :
    P →
    Φ ⟨⟩ -∗
    WPi FailE.assert P @> H;M {{ Φ }} := by
  intro hP; unfold FailE.assert; simp [hP]
  iintro HΦ; iapply wpi_pure $$ HΦ

end wpi_rules

section exec

open ITree.Exec

instance failEH_adequate {PROP : Type _} [BI PROP] [BIFUpdate PROP] :
    SEHandlerAdequate (failH (PROP := PROP)) failEH where
  inv _ := iprop(True)
  adequate := by
    intro i s C Φ1 Φ2 Hhandle; simp [failH]
    iintro ⟨⟩

end exec
