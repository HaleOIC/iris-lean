module

public import IrisITree.Core.ITree
public import ITree.Definition
public import ITree.Effect

@[expose] public section

open ITree

namespace IrisITree.Core

/- A [trace] records one finite execution path of an `ITree`. Silent `tau` steps are ignored. -/
inductive trace (E : Effect) (R : Type _) where
  /-- Return a value. -/
  | trRet (r : R)
  /-- Emit an event, observe one answer, and continue with the rest of the trace. -/
  | trVis (i : E.I) (a : E.O i) (k : trace E R)
  /-- Emit an event with no possible answers and halt the trace there. -/
  | trVisHalt (i : E.I)
  /-- Discontinue the trace. -/
  | trCut

section is_trace

variable {E : Effect} {R : Type _}

inductive is_trace_ : trace E R → ITreeF E R (ITree E R) → Prop where
  | trace_trRet (r : R) : is_trace_ (.trRet r) (.ret r)
  | trace_trVis (tr' : trace E R) (i : E.I) (a : E.O i) (k : E.O i → ITree E R) :
      is_trace_ tr' (ITree.unfold (k a)) → is_trace_ (.trVis i a tr') (.vis i k)
  | trace_trVisHalt (i : E.I) (k : E.O i → ITree E R) :
      is_trace_ (.trVisHalt i) (.vis i k)
  | trace_trCut (t : ITreeF E R (ITree E R)) : is_trace_ .trCut t
  | trace_tau (tr : trace E R) (t : ITree E R) :
      is_trace_ tr (t.unfold) → is_trace_ tr (.tau t)

/-- [tr] is a valid trace in [t]. -/
def is_trace (tr : trace E R) (t : ITree E R) : Prop :=
  is_trace_ tr (t.unfold)

/-- Silent steps can always be added to and removed from a valid trace. -/
theorem is_trace_tau_iff {tr : trace E R} {t : ITree E R} :
    is_trace tr t ↔ is_trace tr (t.tau) := by
  constructor
  . intro h; exact is_trace_.trace_tau tr t h
  . intro h; simp [is_trace] at h
    cases h with
    | trace_tau _ _ h' => exact h'
    | trace_trCut _ => exact is_trace_.trace_trCut (t.unfold)

/-- Equality-specialized equivalence for traces. -/
theorem is_trace_congr_iff (tr : trace E R) {t₁ t₂ : ITree E R} (ht : t₁ = t₂) :
    is_trace tr t₁ ↔ is_trace tr t₂ := by
  subst ht
  exact Iff.rfl

theorem is_trace_Vis (i : E.I) (a : E.O i) (tr' : trace E R) (k : E.O i → ITree E R) :
    is_trace tr' (k a) → is_trace (.trVis i a tr') (.vis i k) := by
  intro htr
  exact is_trace_.trace_trVis tr' i a k htr

end is_trace

section decidable_eq

/-- Event interfaces whose answer type has decidable equality at every input. -/
class AnswerEqDecision (E : Effect) where
  is_AnswerEqDecision : (i : E.I) → DecidableEq (E.O i)

attribute [instance] AnswerEqDecision.is_AnswerEqDecision

instance AnswerEqDecisionSum (E E' : Effect) [AnswerEqDecision E] [AnswerEqDecision E'] :
    AnswerEqDecision (E ⊕ₑ E') where
  is_AnswerEqDecision
  | .inl i => AnswerEqDecision.is_AnswerEqDecision i
  | .inr i => AnswerEqDecision.is_AnswerEqDecision i

def equal {E : Effect} [AnswerEqDecision E] (i : E.I) (a a' : E.O i) :
    Decidable (a = a') := inferInstance

end decidable_eq

/-- Prune the events of `E` from a trace over `E ⊕ₑ E'`. -/
def interp_tr {R : Type _} {E E' : Effect} (tr : trace (E ⊕ₑ E') R) : trace E' R :=
  match tr with
  | .trRet r => .trRet r
  | .trVis (.inl _) _ k => interp_tr k
  | .trVis (.inr i) a k => .trVis i a (interp_tr k)
  | .trVisHalt (.inl _) => .trCut
  | .trVisHalt (.inr i) => .trVisHalt i
  | .trCut => .trCut

section trace_postfix

variable {E : Effect} {R : Type _}

/-- `is_postfix tr tr'` says that `tr` is a postfix of `tr'`. -/
inductive is_postfix : trace E R → trace E R → Prop where
  | is_postfix_same (tr : trace E R) : is_postfix tr tr
  | is_postfix_TVis (tr tr' : trace E R) (i : E.I) (a : E.O i) :
      is_postfix tr tr' → is_postfix tr (.trVis i a tr')

/-- Interpreting away one summand preserves postfixes. -/
theorem interp_tr_is_postfix {E E' : Effect} {R : Type _} :
    ∀ {tr tr' : trace (E ⊕ₑ E') R}, is_postfix tr tr' →
      is_postfix (interp_tr tr) (interp_tr tr')
  | _, _, .is_postfix_same tr =>
      .is_postfix_same (interp_tr tr)
  | _, _, .is_postfix_TVis tr tr' (Sum.inl _) _ h =>
      interp_tr_is_postfix (tr := tr) (tr' := tr') h
  | _, _, .is_postfix_TVis tr tr' (Sum.inr i) a h =>
      .is_postfix_TVis (interp_tr tr) (interp_tr tr') i a
        (interp_tr_is_postfix (tr := tr) (tr' := tr') h)

end trace_postfix

end IrisITree.Core
