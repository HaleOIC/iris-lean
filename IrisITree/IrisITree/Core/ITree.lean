module

public import ITree.Definition

@[expose] public section

namespace ITree

open ITree

variable {E R} (t : ITree E R)

theorem bind_ret (t : ITree E R) :
  t >>= (fun x => ITree.ret x) = t := by
  simpa [Functor.map, pure]
    using (id_map (f := ITree E) (x := t))

theorem match_itree : ∀ (t : ITree E R),
    (∃ r, t = ret r) ∨ (∃ t', t = tau t') ∨ (∃ i k, t = vis i k) := by
  intro t
  cases t with
  | ret r => left; exists r
  | tau t => right; left; exists t
  | vis i k => right; right; exists i, k

@[simp]
theorem interp_ret {F} (f : (i : E.I) → ITree F (E.O i)) (r : R) :
  ITree.interp f (ret r) = ret r := by
    unfold ITree.interp ITree.iter
    simp; rfl

@[simp]
theorem interp_trigger_id (t : ITree E R) :
    ITree.interp (λ i => ITree.trigger E i) t = t := by
  ext n
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
      rcases ITree.match_itree t with ⟨r, rfl⟩ | ⟨t', rfl⟩ | ⟨i, k, rfl⟩
      · simp [interp_ret]
      · simp [interp_tau, ih]
      · simp [interp_vis, ITree.trigger]
        congr
        funext o
        exact ih (k o)

section interp_inverse

theorem interp_ret_inv {E1 E2 R} [sub : E1 -< E2] {t : ITree E1 R} {r : R} :
    ITree.interp (λ i => (ITree.trigger E1 i : ITree E2 (E1.O i))) t = ret r →
    t = ret r := by
  sorry

theorem interp_tau_inv {E1 E2 R} [sub : E1 -< E2] {t : ITree E1 R} {u : ITree E2 R} :
    ITree.interp (λ i => (ITree.trigger E1 i : ITree E2 (E1.O i))) t = tau u →
    ∃ t', t = tau t' ∧ ITree.interp (λ i => (ITree.trigger E1 i : ITree E2 (E1.O i))) t' = u := by
  sorry

theorem interp_vis_inv {E1 E2 R} [sub : E1 -< E2] {t : ITree E1 R} {i : E2.I} {k : E2.O i → ITree E2 R} :
    ITree.interp (λ i => (ITree.trigger E1 i : ITree E2 (E1.O i))) t = vis i k →
    ∃ (i' : E1.I) (k' : E1.O i' → ITree E1 R),
      t = vis i' k' ∧
      i = (sub.map i').fst ∧
      HEq k
        (λ x => ITree.interp (λ i => (ITree.trigger E1 i : ITree E2 (E1.O i)))
          (k' ((sub.map i').snd x))) := by
  sorry

end interp_inverse

end ITree
