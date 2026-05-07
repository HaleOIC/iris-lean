module

public import IrisITree.Core.HandlerAdequate
public import IrisITree.Core.Wpi
public import ITree

@[expose] public section

namespace IrisITree.Effect

open Iris BI ITree Effects

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
  iintro Hwp; simp [fail, ITree.trigger]
  ihave Hwp := wpi_vis' M Φ $$ Hwp
  imod Hwp
  have key : ∀ (Ψ₁ Ψ₂ : failE.O ({ down := s } : failE.I) → PROP),
      H.ihandle (@Subeffect.map failE E sub ({ down := s } : failE.I)).fst
        (fun a => Ψ₁ ((@Subeffect.map failE E sub ({ down := s } : failE.I)).snd a))
        (fun a => Ψ₂ ((@Subeffect.map failE E sub ({ down := s } : failE.I)).snd a)) ⊢
        iprop(False) := by
    intro Ψ₁ Ψ₂
    refine (Hin.is_inH ({ down := s } : failE.I) Ψ₁ Ψ₂).mpr.trans ?_
    exact false_elim
  -- iapply ((key (fun p => wpi (H := H) (R := R) ∅ (nomatch p)
      -- (fun v => iprop(|={∅,M}=> Φ v)))
    -- (fun p => wpi (H := H) (R := R) ⊤ (nomatch p)
      -- (fun _ => iprop(False)))).trans false_elim)
  sorry
  -- iexact Hwp

theorem wpi_assert (M : CoPset) (P : Prop) [Decidable P] (Φ : PUnit → PROP) :
    P → Φ ⟨⟩ ⊢
    (WPi FailE.assert P @> H; M {{ Φ }}) := by
  intro hP
  unfold FailE.assert
  simp [hP]
  iintro HΦ
  iapply wpi_ret (H := H) (M := M) (Φ := Φ) (r := ⟨⟩)
  iexact HΦ


end wpi_rules

section exec

open ITree.Exec IrisITree.Core

instance failEH_adequate {PROP : Type _} [BI PROP] [BIFUpdate PROP] :
    SEHandlerAdequate (failH (PROP := PROP)) failEH where
  sehandler_inv _ := iprop(True)
  sehandler_adequate := by
    intro i s C Φ1 Φ2 Hhandle
    simp [failH]
    iintro Hfalse _
    icases Hfalse with ⟨⟩

theorem exec_some_or_ub {E : Effect} {R σ : Type _}
    (EH : EHandler E E R σ) [failE -< E] [InEH failEH.toEHandler EH]
    (msg : String) (o : Option R) (s : σ) (C : ITree E R → σ → Prop) :
    (∀ x, o = some x → C (ITree.ret x) s) →
    exec EH (match o with | some x => ITree.ret x | none => FailE.fail msg) s C := by
  intro hC; cases o with
  | none => unfold FailE.fail; apply exec.trigger failEH.toEHandler; simp [failEH]
  | some x => apply exec.stop; exact hC x rfl

theorem exec_assert {E : Effect} {σ : Type _}
    (EH : EHandler E E PUnit σ) [failE -< E] [InEH failEH.toEHandler EH]
    (P : Prop) [Decidable P] (s : σ) (C : ITree E PUnit → σ → Prop) :
    (P → C (ITree.ret ⟨⟩) s) →
    exec EH (FailE.assert P) s C := by
  intro hC; unfold FailE.assert
  by_cases h : P
  · simp [h]; apply exec.stop; exact hC h
  · simp [h, FailE.fail]; apply exec.trigger failEH.toEHandler; simp [failEH]

end exec

end IrisITree.Effect
