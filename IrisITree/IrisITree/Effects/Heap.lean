module

public import IrisITree.Effects.State
public import IrisITree.Effects.Demonic
public import IrisITree.Effects.Fail
public import ITree.Effects.Heap
public import Iris.BI.BigOp.BigSepList
public import Iris.Instances.Lib.GhostMap
public import Iris.Instances.Lib.Invariants
public import Iris.Std.HeapInstances

@[expose] public section

-- A heap, represented as a [gmap] of [option val]s, with [None] representing deallocated locations.

namespace IrisITree.Effects

open Iris BI ITree Effects Core

-- TODO: Why can’t we make this universe-polymorphic? `Loc` and `Val` should have type `Type _`
-- The restriction seems to come from `GhostMapG`; More concretely, `constOF` is too conservative.
class heapHGpreS (GF : BundledGFunctors) (Loc Val : Type)
    [Ord Loc] [Std.TransOrd Loc] [Std.LawfulEqOrd Loc] where
  heapH_ghost_varG : GhostMapG GF Loc (Option Val) (Std.ExtTreeMap Loc · compare)

attribute [reducible, instance] heapHGpreS.heapH_ghost_varG

class heapHGS (GF : BundledGFunctors) (Loc Val : Type)
    [Ord Loc] [Std.TransOrd Loc] [Std.LawfulEqOrd Loc] where
  heapH_inG : heapHGpreS GF Loc Val
  heapH_heap_name : GName
  heapH_inv_name_postfix : String

attribute [reducible, instance] heapHGS.heapH_inG

def heapH_inv_name {GF : BundledGFunctors} {Loc Val : Type}
    [Ord Loc] [Std.TransOrd Loc] [Std.LawfulEqOrd Loc]
    [G : heapHGS GF Loc Val] : Namespace :=
  (nroot.@"heapH").@G.heapH_inv_name_postfix

def pointsto {GF : BundledGFunctors} {Loc Val : Type}
    [Ord Loc] [Std.TransOrd Loc] [Std.LawfulEqOrd Loc]
    [G : heapHGS GF Loc Val] (l : Loc) (v : Option Val) (dq : DFrac) : IProp GF :=
  ghost_map_elem (G.heapH_heap_name) dq l v

notation:50 l:50 " ↦? " v:50 => pointsto l v (DFrac.own 1)
notation:50 l:50 " ↦{" dq "}? " v:50 => pointsto l v dq
notation:50 l:50 " ↦ " v:50 => pointsto l (some v) (DFrac.own 1)
notation:50 l:50 " ↦{" dq "} " v:50 => pointsto l (some v) dq

section handler

variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
variable {Loc Val : Type} [Ord Loc] [Std.TransOrd Loc] [Std.LawfulEqOrd Loc] [DecidableEq Loc]
variable [G : heapHGS GF Loc Val]

-- Half of the authoritative view of the current heap into an invariant
-- so that we can know that someone else won't change it while we have control
def heap_inv : IProp GF :=
  inv (heapH_inv_name (G := G)) iprop(
    ∃ σ, ghost_map_auth (K := Loc) (V := Option Val)
      G.heapH_heap_name (DFrac.own $ Qp.half 1) σ
  )

instance heap_inv_persistent : Persistent (heap_inv (G := G)) := by
  unfold heap_inv
  infer_instance

def stateInterp_heap (σ : heapE.T Loc Val) : IProp GF := iprop(
  ghost_map_auth (K := Loc) (V := Option Val)
    G.heapH_heap_name (DFrac.own $ Qp.half 1) σ
  ∧ heap_inv (G := G)
)

def heapH : IHandler (IProp GF) (heapE Loc Val) :=
  stateH stateInterp_heap

end handler

section initialization

variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
variable {Loc Val : Type} [Ord Loc] [Std.TransOrd Loc] [Std.LawfulEqOrd Loc] [DecidableEq Loc]
variable [Gpre : heapHGpreS GF Loc Val]

-- TODO: find way to eliminate the parameter M and use the syntax sugar instead of `bigSepM`
theorem heapH_init  (σ : heapE.T Loc Val) :
    ⊢ |={∅}=> ∃ G : heapHGS GF Loc Val,
      heap_inv (G := G) ∗
      stateInterp_heap σ ∗
      bigSepM (M := (Std.ExtTreeMap Loc · compare)) (λ k v => k ↦? v) σ := by
  icases (ghost_map_alloc (K := Loc) (V := Option Val) σ) with Hgmap
  imod Hgmap; icases Hgmap with ⟨%γ, ⟨⟨Hauth, Hauth'⟩, Hfrag⟩⟩
  imod (inv_alloc ((nroot.@"heapH").@"") ∅
    (∃ σ, ghost_map_auth (K := Loc) (V := Option Val) γ (.own $ .half 1) σ)) $$ [Hauth] with #Hinv
  · inext; iexists σ; iassumption
  · imodintro; iexists ⟨Gpre, γ, ""⟩
    unfold heap_inv heapH_inv_name stateInterp_heap pointsto
    isplitr
    · iassumption
    isplitl [Hauth']
    · isplit; iassumption
      unfold heap_inv heapH_inv_name
      iassumption
    · iframe

end initialization

section wpi_rules

variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
variable {Loc Val : Type} [Ord Loc] [Std.TransOrd Loc] [Std.LawfulEqOrd Loc]
variable [G : heapHGS GF Loc Val]
variable {E : Effect} {H : IHandler (IProp GF) E}
variable [heapE Loc Val -< E] [InH (heapH (G := G)) H]

-- Note: we can extend the following theorems to `Ms,Me` version by having `|={Ms,Me}=> Φ v`
theorem wpi_storeOpt M (l : Loc) (v v' : Option Val) (Φ : Option Val → IProp GF) :
    ↑(heapH_inv_name (G := G)) ⊆ M →
    l ↦? v -∗
    (l ↦? v' -∗ Φ v) -∗
    WPi (storeOpt l v') @> H; M {{ Φ }} := by
  iintro %Hmask Hpt Hwand; unfold pointsto storeOpt
  iapply wpi_bind' (M \ ↑(heapH_inv_name (G := G))); iapply wpi_get
  unfold stateInterp_heap heap_inv
  iintro %σ ⟨HauthState, #Hinv⟩
  imod inv_acc_timeless Hmask $$ Hinv with ⟨⟨%σinv, HauthInv⟩, Hclose⟩
  ihave %Heq := ghost_map_auth_agree $$ HauthInv HauthState; subst σinv
  imodintro; isplitl [HauthState]
  · isplit <;> iassumption

  -- look up and insert operations
  ihave %Hlookup := ghost_map_lookup $$ HauthInv Hpt
  have Hlookup : σ[l]? = some v := by
    simpa [Iris.Std.get?] using Hlookup
  have Hinsert : σ.insert l v' = Std.insert (M := (Std.ExtTreeMap Loc · compare)) σ l v'  := by
    apply Std.ExtTreeMap.ext_getElem?; intro k
    simp only [Iris.Std.insert, Std.ExtTreeMap.getElem?_alter, Std.ExtTreeMap.getElem?_insert]
  rw [Hlookup, Hinsert]

  iapply wpi_bind' M; iapply wpi_set
  unfold stateInterp_heap heap_inv
  iintro %σ' ⟨HauthState, -⟩
  ihave %Heq := ghost_map_auth_agree $$ HauthInv HauthState; subst σ'
  icombine HauthInv HauthState as Hauth; rw [Qp.half_add_half (1 : Qp)]
  imod ghost_map_update v' $$ Hauth Hpt with ⟨⟨Hauth, Hauth'⟩, Hpt⟩
  imod Hclose $$ [Hauth'] with -
  · iexists Std.insert (M := (Std.ExtTreeMap Loc · compare)) σ l v'
    iexact Hauth'
  imodintro; isplitl [Hauth]
  · isplit <;> iassumption
  iapply wpi_pure; simp only [Option.join_some]
  iapply Hwand $$ [$]

theorem wpi_store? M (l : Loc) (v : Option Val) (v' : Val) (Φ : Option Val → IProp GF) :
    ↑(heapH_inv_name (G := G)) ⊆ M →
    l ↦? v -∗
    (l ↦ v' -∗ Φ v) -∗
    WPi (store? l v') @> H; M {{ Φ }} := by
  iintro %Hmask Hpt Hwand; unfold store?
  iapply wpi_storeOpt _ _ _ _ _ Hmask $$ Hpt Hwand

theorem wpi_load? M (l : Loc) (v : Val) (dq : DFrac) (Φ : Option Val → IProp GF) :
    ↑(heapH_inv_name (G := G)) ⊆ M →
    l ↦{dq} v -∗
    (l ↦{dq} v -∗ Φ (some v)) -∗
    WPi (load? l) @> H; M {{ Φ }} := by
  iintro %Hmask Hpt Hwand; unfold pointsto load?
  iapply wpi_bind; iapply wpi_get
  unfold stateInterp_heap heap_inv
  iintro %σ ⟨Hauth, #Hinv⟩

  ihave %Hlookup := ghost_map_lookup $$ Hauth Hpt
  have Hlookup : σ[l]? = some (some v) := by
    simpa [Iris.Std.get?] using Hlookup
  rw [Hlookup]; simp only [Option.join_some]

  iframe; iframe Hinv
  imodintro; iapply wpi_pure
  iapply Hwand $$ [$]

section fail

variable [failE -< E]

theorem wpi_store! M (l : Loc) (v v' : Val) (Φ : Val → IProp GF) :
    ↑(heapH_inv_name (G := G)) ⊆ M →
    l ↦ v -∗
    (l ↦ v' -∗ Φ v) -∗
    WPi (store! l v') @> H; M {{ Φ }} := by
  iintro %Hmask Hpt Hwand; unfold store!
  iapply wpi_bind; iapply wpi_store? _ _ _ _ _ Hmask $$ Hpt
  iintro Hpt; iapply wpi_pure; iapply Hwand $$ [$]

theorem wpi_load! M (l : Loc) (v : Val) (dq : DFrac) (Φ : Val → IProp GF) :
    ↑(heapH_inv_name (G := G)) ⊆ M →
    l ↦{dq} v -∗
    (l ↦{dq} v -∗ Φ v) -∗
    WPi (load! l) @> H; M {{ Φ }} := by
  iintro %Hmask Hpt Hwand; unfold load!
  iapply wpi_bind; iapply wpi_load? _ _ _ _ _ Hmask $$ Hpt
  iintro Hpt; iapply wpi_pure; iapply Hwand $$ Hpt

end fail

section alloc

variable [demonicE Loc -< E] [InH (demonicH (PROP := IProp GF) Loc) H]
variable [Zero Loc] [HAdd Loc Int Loc]

theorem wpi_allocN M (n : Nat) (v : Val)
    (hle : ∀ (l : Loc) (m : Nat), ¬(compare (l + (1 : Int) + (m : Int)) l).isLE = true)
    (Φ : Loc → IProp GF) :
    ↑(heapH_inv_name (GF := GF) (Loc := Loc) (Val := Val)) ⊆ M →
    (∀ l : Loc,
      bigSepL (fun _ (i : Nat) =>
        pointsto (GF := GF) (Loc := Loc) (Val := Val)
          (l + (i : Int)) (some v) (DFrac.own (1 : Qp))) (List.range n) -∗ Φ l) -∗
    WPi (HeapE.allocN (E := E) (Loc := Loc) (Val := Val) n v hle) @> H; M {{ Φ }} := by
  sorry

theorem wpi_alloc M (v : Val)
    (hle : ∀ (l : Loc) (m : Nat), ¬(compare (l + (1 : Int) + (m : Int)) l).isLE = true)
    (Φ : Loc → IProp GF) :
    ↑(heapH_inv_name (GF := GF) (Loc := Loc) (Val := Val)) ⊆ M →
    (∀ l : Loc,
      pointsto (GF := GF) (Loc := Loc) (Val := Val) l (some v) (DFrac.own (1 : Qp)) -∗ Φ l) -∗
    WPi (HeapE.alloc (E := E) (Loc := Loc) (Val := Val) v hle) @> H; M {{ Φ }} := by
  sorry

end alloc

end wpi_rules

end IrisITree.Effects
