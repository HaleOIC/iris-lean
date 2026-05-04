module

public import IrisITree.Core.WpiMask
public import IrisITree.Core.WpiExec
public import Iris.Instances.Lib.FUpd

@[expose] public section

namespace IrisITree.Core

open Iris BI ITree Std OFE

open ITree.Exec

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]

public class EHandlerAdequate {E GE : Effect.{u} } {R σ : Type _}
    (H : IHandler (PROP := PROP) E) (EH : EHandler E GE R σ) where
  ehandler_inv : σ → List (((ITree GE R → PROP) → PROP)) → PROP
  ehandler_adequate :
    ∀ (G : ITree GE R → PROP) (i : E.I) (s : σ)
      (Ms : List (((ITree GE R → PROP) → PROP)))
      (C : ITree GE R → σ → Prop) (k : E.O i → ITree GE R),
      EH.handle i s k C →
      H.ihandle i (λ a => G (k a)) (λ a => iprop(|={⊤,∅}=> G (k a))) ⊢
      ehandler_inv s Ms -∗
      |={∅}=> ∃ t' s' M' Ms' Msn, ⌜C t' s'⌝ ∗ ⌜(M' :: Ms').Perm (Msn ++ Ms)⌝ ∗
        ([∗list] M ∈ Msn, M G) ∗ ehandler_inv s' Ms' ∗
        bi_close Eq (λ t'' => iprop(∀ P, M' P ={∅}=∗ P t'')) t'
  ehandler_inv_proper : ∀ {s s' Ms Ms'}, s = s' → Ms = Ms' →
    ehandler_inv s Ms ⊢ ehandler_inv s' Ms'

/-- Logical adequacy interface for simple executable handlers. -/
public class SEHandlerAdequate {E : Effect.{u} } {σ : Type _}
    (H : IHandler (PROP := PROP) E) (EH : SEHandler E σ) where
  sehandler_inv : σ → PROP
  sehandler_adequate :
    ∀ (i : E.I) (s : σ) (C : E.O i → σ → Prop) (Φ1 Φ2 : E.O i → PROP),
      EH.handle i s C →
      H.ihandle i Φ1 Φ2 ⊢
      sehandler_inv s -∗
      |={∅}=> ∃ a s', ⌜C a s'⌝ ∗ sehandler_inv s' ∗ Φ1 a

instance handler_adequate_from_simple {E GE : Effect.{u} } {R σ : Type _}
    (H : IHandler (PROP := PROP) E) (EH : SEHandler E σ)
    [A : SEHandlerAdequate (PROP := PROP) H EH] :
    EHandlerAdequate (PROP := PROP) (GE := GE) (R := R) H (EH : EHandler E GE R σ) where
  ehandler_inv s _ := A.sehandler_inv s
  ehandler_adequate := by
    intro G i s Ms C k H0; simp at H0
    apply (A.sehandler_adequate i s _ _ _ H0).trans
    iintro Hstep Hinv; ispecialize Hstep $$ Hinv
    iapply BIFUpdate.mono $$ Hstep
    iintro Hpost; icases Hpost with ⟨%a, %s', HC, Hs, HG⟩; ipure HC
    iexists (k a), s', (λ P => P (k a)), Ms, [λ P => P (k a)]
    isplitl []; ipure_intro; exact HC
    isplitl []; ipure_intro; simp
    isplitl [HG]; simp; isplitl [HG]; iexact HG; simp
    isplitl [Hs]; iexact Hs
    simp only [bi_close]; iexists (k a);
    isplitl []; ipure_intro; simp
    iintro %P Hp; imodintro; iexact Hp
  ehandler_inv_proper := by
    intro s s' Ms Ms' hs hMs
    cases hs; cases hMs
    iintro Hinv; iexact Hinv

section wpi_adequate

open ITree.Exec

variable {E : Effect.{u} } {R : Type u} {σ : Type _} [BIAffine PROP]

theorem wpi_adequate_ind (Φ : R → PROP) (H : IHandler (PROP := PROP) E)
    (EH : EHandler E E R σ) [A : EHandlerAdequate (PROP := PROP) H EH]
    (t : ITree E R) (s : σ)
    (Ms : List (((LeibnizO (ITree E R) → PROP) → PROP)))
    (Mss : List (((ITree E R → PROP) → PROP)))
    (M : (LeibnizO (ITree E R) → PROP) → PROP)
    (C : ITree E R → σ → Prop)
    (Hexec : exec EH t s C)
    (HMs : Ms.Perm (M :: Mss.map (λ M' P => M' (λ t => P ⟨t⟩)))) :
    ⊢ wpi_tp H Ms Φ -∗
      A.ehandler_inv s Mss -∗
      (∀ P, M P ={∅}=∗ P ⟨t⟩) -∗
      |={∅}=> ∃ t' s' Ms' M',
        ⌜C t' s'⌝ ∗
        A.ehandler_inv s' Ms' ∗
        bi_close Eq (λ t'' => iprop(∀ P, M' P ={∅}=∗ P t'')) ⟨t'⟩ ∗
        wpi_tp H (M' :: Ms'.map (λ M'' P => M'' (λ t => P ⟨t⟩))) Φ := by
  sorry

theorem wpi_adequate (Φ : R → PROP) (H : IHandler (PROP := PROP) E)
    (EH : EHandler E E R σ) [A : EHandlerAdequate (PROP := PROP) H EH]
    (t : ITree E R) (s : σ)
    (C : ITree E R → σ → Prop) (m : CoPset)
    (Hexec : exec EH t s C) :
    ⊢ iprop(|={m,∅}=> wpi H t (λ v => iprop(|={∅,m}=> Φ v))) -∗
      A.ehandler_inv s [] -∗
      |={m, ∅}=> ∃ t' s' Ms' M',
      ⌜C t' s'⌝ ∗
      A.ehandler_inv s' Ms' ∗
      bi_close Eq (λ t'' => iprop(∀ P, M' P ={∅}=∗ P t'')) ⟨t'⟩ ∗
      wpi_tp H (M' :: Ms'.map (λ M'' P => M'' (λ t => P ⟨t⟩))) (λ v => iprop(|={∅,m}=> Φ v)) := by
  sorry

end wpi_adequate

end IrisITree.Core
