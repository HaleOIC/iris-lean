module

public import IrisITree.Core.HandlerAdequate
public import IrisITree.Core.WpiMask
public import ITree.Effects.State

@[expose] public section

namespace IrisITree.Event

open Iris BI ITree Effects

section handler

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]

def stateH {S : Type _} (state_interp : S → PROP) : IHandler (PROP := PROP) (stateE S) where
  ihandle := fun i Φ _ => iprop(∀ s, state_interp s ={∅}=∗ state_interp (i s) ∗ Φ s)
  ihandle_mono := by
    iintro %i %Φ %Φ' %s %s' HΦwand #Hswand HH
    iintro %st Hst; ispecialize HH $$ Hst
    imod HH; imodintro; icases HH with ⟨Hst, HΦ⟩
    isplitl [Hst]
    · iexact Hst
    · iapply HΦwand $$ HΦ

instance stateH_sequential {S : Type _} (state_interp : S → PROP) :
    Sequential (PROP := PROP) (stateH (PROP := PROP) state_interp) := by
  constructor
  iintro %i %Φ %s HH
  simp [stateH]

end handler

section wpi_rules

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP] {S : Type _}
  (state_interp : S → PROP)
  {E : Effect} {H : IHandler (PROP := PROP) E}
  [stateE S -< E] [Hin : InH (stateH (PROP := PROP) state_interp) H]

theorem wpi_get_state (M : CoPset) (Φ : S → PROP) :
    ⊢ (∀ s, state_interp s ={∅}=∗ state_interp s ∗ Φ s) -∗
      wpi_mask (H := H) M (StateE.get (α := S)) Φ := by
  let m : Σ i : E.I, E.O i → S := @Subeffect.map (stateE S) E _ (id : S → S)
  have Hvis :
      ⊢ (∀ s, state_interp s ={∅}=∗ state_interp s ∗ Φ s) -∗
        (WPi
          (ITree.vis m.1 (fun x : E.O m.1 => ITree.ret (m.2 x))) @> H; M {{ Φ }}) := by
    iintro HΦ
    iapply (wpi_vis (H := H) (M := M) (Φ := Φ)
      (i := m.1)
      (k := fun x : E.O m.1 => ITree.ret (m.2 x)))
    iapply fupd_mask_intro
    · exact Std.LawfulSet.empty_subset
    · iintro Hfupd
      let Φ1 : S → PROP := fun a =>
        WPi ITree.ret a @> H; ∅ {{ fun v => iprop(|={∅,M}=> Φ v) }}
      let Φ2 : S → PROP := fun a =>
        WPi ITree.ret a @> H; ⊤ {{ fun _ => iprop(False) }}
      have HIn :
          (stateH (PROP := PROP) state_interp).ihandle (id : S → S) Φ1 Φ2 ⊢
            H.ihandle m.1 (fun a => Φ1 (m.2 a)) (fun a => Φ2 (m.2 a)) := by
        exact (Hin.is_inH (i₁ := (id : S → S)) (Φ₁ := Φ1) (s₁ := Φ2)).mp
      iapply HIn
      simp [stateH]
      iintro %s Hs
      ispecialize HΦ $$ %s Hs
      imod HΦ
      icases HΦ with ⟨Hs, HΦs⟩
      imodintro
      isplitl [Hs]
      · iexact Hs
      · iapply (wpi_ret' (H := H) (M := ∅)
          (Φ := fun v => iprop(|={∅,M}=> Φ v)) (r := s)).mp
        imodintro
        imod Hfupd
        imodintro
        iexact HΦs
  simpa [m, StateE.get, StateE.modify, ITree.trigger] using Hvis

theorem wpi_set_state (st' : S) (M : CoPset) (Ψ : PUnit → PROP) :
    ⊢ (∀ s, state_interp s ={∅}=∗ state_interp st' ∗ Ψ PUnit.unit) -∗
      wpi_mask (H := H) M (StateE.set (α := S) st') Ψ := by
  sorry

end wpi_rules

end IrisITree.Event
