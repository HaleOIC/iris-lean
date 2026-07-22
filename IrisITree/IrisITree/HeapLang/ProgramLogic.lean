module

public import IrisITree.Core.Wpi
public import IrisITree.Effects
public import IrisITree.HeapLang.Semantics
public import Iris.BI.WeakestPre
public import Iris.Instances.IProp
public import Iris.Instances.Lib.FUpd

@[expose] public section
namespace IrisITree.HeapLang

open Iris IrisITree.Core Iris.HeapLang IrisITree.Effects

section wp
variable {GF} [InvGS GF] {m : Unit}

def heaplangH : IHandler (IProp GF) heaplangE := concH ⊕ₕ (by sorry) ⊕ₕ failH ⊕ₕ demonicH Loc ⊕ₕ by sorry

instance wp_heaplang : Wp (IProp GF) Exp Val Unit where
  wp _ E e Φ := WPi e.denote @> heaplangH; E {{ Φ }}

theorem wp_unfold (e : Exp) (Φ : Val → IProp GF) :
  WP e @ m ; E {{ Φ }} = WPi e.denote @> heaplangH; E {{ Φ }} := rfl

-- TODO
/-
  Lemma wp_bind m K e Φ :
    WP e @ m; ⊤ {{ v,
      WP fill K (Val v) @ m; ⊤ {{ Φ }}
    }} -∗
    WP fill K e @ m; ⊤ {{ Φ }}.
-/

theorem wp_wand E (e : Exp) (Φ Ψ : Val → IProp GF) :
  WP e @ m ; E {{ Φ }} -∗
  (∀ v, Φ v -∗ Ψ v) -∗
  WP e @ m ; E {{ Ψ }} := by
    simp only [wp_unfold]
    apply wpi_wand

theorem wp_atomic E1 E2 (e : Exp) (Φ : Val → IProp GF) :
  (|={E1,E2}=> WP e @ m ; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢
  WP e @ m ; E1 {{ Φ }} := by
    simp only [wp_unfold]
    iintro > >Hwp
    iapply wpi_fupd_empty
    ihave Hwp := wpi_fupd_empty $$ Hwp
    iapply wpi_wand $$ Hwp
    iintro %_ > > $

theorem fupd_wp E (e : Exp) (Φ : Val → IProp GF) :
  (|={E}=> WP e @ m ; E {{ v, Φ v }}) ⊢ WP e @ m ; E {{ Φ }} := by
    simp only [wp_unfold]
    iapply (fupd_wpi _).2

theorem wp_fupd E (e : Exp) (Φ : Val → IProp GF) :
  (WP e @ m ; E {{ v, |={E}=> Φ v }}) ⊢ WP e @ m ; E {{ Φ }} := by
    simp only [wp_unfold]
    iapply (wpi_fupd _).2

-- # Proof rules for pure operations

theorem wp_val E (v : Val) (Φ : Val → IProp GF) :
    Φ v -∗
    WP hl(v(&v)) @ m ; E {{ Φ }} := by
  sorry
  -- simp only [wp_unfold, Exp.denote]
  -- iapply wpi_pure

-- TODO...

end wp
