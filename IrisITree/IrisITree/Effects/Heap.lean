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
variable {Loc Val : Type} [Ord Loc] [Std.TransOrd Loc] [Std.LawfulEqOrd Loc]
variable [G : heapHGS GF Loc Val]

def heap_inv : IProp GF :=
  inv (heapH_inv_name (G := G)) iprop(
    ∃ σ : heapE.T Loc Val,
      ghost_map_auth (GF := GF) (K := Loc) (V := Option Val)
        (H := (Std.ExtTreeMap Loc · compare))
        G.heapH_heap_name
        (DFrac.own (Qp.half (1 : Qp))) σ
  )

def stateInterp_heap (σ : heapE.T Loc Val) : IProp GF := iprop(
  ghost_map_auth (GF := GF) (K := Loc) (V := Option Val)
      (H := (Std.ExtTreeMap Loc · compare))
      G.heapH_heap_name
      (DFrac.own (Qp.half (1 : Qp))) σ ∧
    heap_inv (G := G)
)

def heapH : IHandler (IProp GF) (heapE Loc Val) :=
  stateH stateInterp_heap

end handler

section wpi_rules

variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
variable {Loc Val : Type} [Ord Loc] [Std.TransOrd Loc] [Std.LawfulEqOrd Loc]
variable [heapHGS GF Loc Val]
variable {E : Effect} {H : IHandler (IProp GF) E}
variable [heapE Loc Val -< E]
variable [InH (heapH (GF := GF) (hlc := hlc) (Loc := Loc) (Val := Val)) H]

theorem wpi_load_opt M (l : Loc) (v : Val) (dq : DFrac)
    (Φ : Option Val → IProp GF) :
    ↑(heapH_inv_name (GF := GF) (Loc := Loc) (Val := Val)) ⊆ M →
    pointsto (GF := GF) (Loc := Loc) (Val := Val) l (some v) dq -∗
    (pointsto (GF := GF) (Loc := Loc) (Val := Val) l (some v) dq -∗ Φ (some v)) -∗
    WPi (HeapE.load? (E := E) (Loc := Loc) (Val := Val) l) @> H; M {{ Φ }} := by
  sorry

theorem wpi_storeOpt M (l : Loc) (v v' : Option Val)
    (Φ : Option Val → IProp GF) :
    ↑(heapH_inv_name (GF := GF) (Loc := Loc) (Val := Val)) ⊆ M →
    pointsto (GF := GF) (Loc := Loc) (Val := Val) l v (DFrac.own (1 : Qp)) -∗
    (pointsto (GF := GF) (Loc := Loc) (Val := Val) l v' (DFrac.own (1 : Qp)) -∗ Φ v) -∗
    WPi (HeapE.storeOpt (E := E) (Loc := Loc) (Val := Val) l v') @> H; M {{ Φ }} := by
  sorry

theorem wpi_store M (l : Loc) (v : Option Val) (v' : Val)
    (Φ : Option Val → IProp GF) :
    ↑(heapH_inv_name (GF := GF) (Loc := Loc) (Val := Val)) ⊆ M →
    pointsto (GF := GF) (Loc := Loc) (Val := Val) l v (DFrac.own (1 : Qp)) -∗
    (pointsto (GF := GF) (Loc := Loc) (Val := Val) l (some v') (DFrac.own (1 : Qp)) -∗ Φ v) -∗
    WPi (HeapE.store? (E := E) (Loc := Loc) (Val := Val) l v') @> H; M {{ Φ }} := by
  sorry

section fail

variable [failE -< E] [InH (failH (PROP := IProp GF)) H]

theorem wpi_load_bang M (l : Loc) (v : Val) (dq : DFrac)
    (Φ : Val → IProp GF) :
    ↑(heapH_inv_name (GF := GF) (Loc := Loc) (Val := Val)) ⊆ M →
    pointsto (GF := GF) (Loc := Loc) (Val := Val) l (some v) dq -∗
    (pointsto (GF := GF) (Loc := Loc) (Val := Val) l (some v) dq -∗ Φ v) -∗
    WPi (HeapE.load! (E := E) (Loc := Loc) (Val := Val) l) @> H; M {{ Φ }} := by
  sorry

theorem wpi_store_bang M (l : Loc) (v v' : Val) (Φ : Val → IProp GF) :
    ↑(heapH_inv_name (GF := GF) (Loc := Loc) (Val := Val)) ⊆ M →
    pointsto (GF := GF) (Loc := Loc) (Val := Val) l (some v) (DFrac.own (1 : Qp)) -∗
    (pointsto (GF := GF) (Loc := Loc) (Val := Val) l (some v') (DFrac.own (1 : Qp)) -∗ Φ v) -∗
    WPi (HeapE.store! (E := E) (Loc := Loc) (Val := Val) l v') @> H; M {{ Φ }} := by
  sorry

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
