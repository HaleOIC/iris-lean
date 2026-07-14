module

public import Iris.Algebra.OFE
public import ITree.Definition

@[expose] public section

namespace IrisITree
open ITree Iris

instance {E R} : COFE (ITree E R) := COFE.ofDiscrete _
instance {E R} : OFE.Discrete (ITree E R) := ⟨λ h _ => h⟩

end IrisITree

-- TODO: upstream?
namespace ITree

open ITree

variable {E R} (t : ITree E R)

@[simp]
theorem interp_trigger_id (t : ITree E R) :
    ITree.interp (λ i => E.trigger i) t = t := by
  ext n
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    cases t <;> simp [ih]
    simp [Effect.trigger]
    congr
    funext o
    apply ih

section interp_inverse

theorem interp_ret_inv {E1 E2 R} [E1 -< E2] {t : ITree E1 R} {r : R} :
    ITree.interp (λ i => (E1.trigger i : ITree E2 (E1.O i))) t = ret r →
    t = ret r := by
  intro h
  cases t <;> simp only [Effect.trigger] at h ⊢
    <;> have h' := congrArg ITree.unfold h
    <;> simp at h'
  subst h'; rfl

theorem interp_tau_inv {E1 E2 R} [E1 -< E2] {t : ITree E1 R} {u : ITree E2 R} :
    ITree.interp (λ i => (E1.trigger i : ITree E2 (E1.O i))) t = tau u →
    ∃ t', t = tau t' ∧ ITree.interp (λ i => (E1.trigger i : ITree E2 (E1.O i))) t' = u := by
  intro h
  cases t <;> simp [Effect.trigger] at h ⊢
    <;> have h' := congrArg ITree.unfold h
    <;> simp at h'
  exact ⟨_, rfl, h'⟩

theorem interp_vis_inv {E1 E2 R} [sub : E1 -< E2] {t : ITree E1 R} {i : E2.I} {k : E2.O i → ITree E2 R} :
    ITree.interp (λ i => (E1.trigger i : ITree E2 (E1.O i))) t = vis i k →
    ∃ (i' : E1.I) (k' : E1.O i' → ITree E1 R),
      t = vis i' k' ∧ i = (sub.map i').fst ∧
      HEq k (λ x => ITree.interp (λ i => (E1.trigger i : ITree E2 (E1.O i))) (k' ((sub.map i').snd x))) := by
  intro h
  cases t <;> simp [Effect.trigger] at h ⊢
    <;> have h' := congrArg ITree.unfold h
    <;> simp at h'
  exact ⟨_, _, rfl, h'.1.symm, h'.2.symm⟩

end interp_inverse

end ITree
