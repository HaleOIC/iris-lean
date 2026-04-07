/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Michael Sammler
-/
module

public meta import Iris.ProofMode.Patterns.ProofModeTerm
public meta import Iris.ProofMode.Patterns.CasesPattern
public meta import Iris.ProofMode.Tactics.Basic

namespace Iris.ProofMode

public section
open BI

theorem specialize_forall [BI PROP] {p : Bool} {A1 A2 P : PROP} {α : Sort _} {Φ : α → PROP}
    [inst : IntoForall P Φ] (h : A1 ⊢ A2 ∗ □?p P) (a : α) : A1 ⊢ A2 ∗ □?p (Φ a) := by
  refine h.trans <| sep_mono_r <| intuitionisticallyIf_mono <| inst.1.trans (forall_elim a)

theorem specialize_wand [BI PROP] {q p : Bool} {A1 A2 A3 Q P1 P2 : PROP}
    (h1 : A1 ⊢ A2 ∗ □?q Q) (h2 : A2 ⊣⊢ A3 ∗ □?p P1)
    [h3 : IntoWand q p Q .in P1 .out P2] :
    A1 ⊢ A3 ∗ □?(p && q) P2 := by
  refine h1.trans <| (sep_mono_l h2.1).trans <| sep_assoc.1.trans (sep_mono_r ?_)
  cases p with
  | false => exact (sep_mono_r h3.1).trans <| wand_elim_r
  | true => exact
    (sep_mono intuitionisticallyIf_intutitionistically.2 intuitionisticallyIf_idem.2).trans <|
    intuitionisticallyIf_sep_2.trans <| intuitionisticallyIf_mono <| (wand_elim' h3.1)

theorem specialize_subgoal [BI PROP] {q : Bool} {A1 A2 A3 A4 Q P1 P2 : PROP}
    (h1 : A1 ⊢ A2 ∗ □?q Q) (h2 : A2 ⊣⊢ A3 ∗ A4) (h3 : A4 ⊢ P1)
    [inst : IntoWand q false Q .out P1 .out P2] : A1 ⊢ A3 ∗ P2 := by
  refine h1.trans <| (sep_mono_l h2.1).trans <| sep_assoc.1.trans (sep_mono_r ((sep_mono_l h3).trans ?_))
  exact (sep_mono_r inst.1).trans wand_elim_r

theorem specialize_subgoal_intuitionistic [BI PROP] [BIPositive PROP] {A1 A2 A3 A4 Q P1 P2 : PROP}
    [Intuitionistic A1] (h1 : A1 ⊢ A2 ∗ □ Q) (h2 : A2 ⊣⊢ A3 ∗ A4) (h3 : A4 ⊢ P1)
    [inst : IntoWand true false Q .out P1 .out P2] : A1 ⊢ A3 ∗ □ P2 := by
  have hbase : A1 ⊢ A3 ∗ P2 := specialize_subgoal (q := true) h1 h2 h3
  refine (intuitionistic.trans <| intuitionistically_mono hbase).trans ?_
  exact (intuitionistically_sep.1).trans <| sep_mono_l intuitionistically_elim

theorem specialize_subgoal_modal [BI PROP] {q : Bool} {A1 A2 A3 A4 Q P1 P1' P2 : PROP}
    (h1 : A1 ⊢ A2 ∗ □?q Q) (h2 : A2 ⊣⊢ A3 ∗ A4) (h3 : A4 ⊢ P1')
    [inst : IntoWand q false Q .out P1 .out P2]
    [hmod : AddModal P1' P1 P2] : A1 ⊢ A3 ∗ P2 := by
  refine h1.trans <| (sep_mono_l h2.1).trans <| sep_assoc.1.trans (sep_mono_r ((sep_mono_l h3).trans ?_))
  exact (sep_mono_r inst.1).trans hmod.1

theorem specialize_subgoal_persistent [BI PROP] {q : Bool} {A1 A2 Q P1 P1' P2 : PROP}
    (h1 : A1 ⊢ A2 ∗ □?q Q) (h2 : A2 ⊢ P1')
    [inst : IntoWand q true Q .in P1 .out P2]
    [Persistent P1] [habs : IntoAbsorbingly P1' P1] :
    A1 ⊢ A2 ∗ □?q P2 := by
  have hprem : A2 ⊢ A2 ∗ □ P1 := (and_intro .rfl <| h2.trans <| habs.1.trans <|
    (absorbingly_mono persistent).trans absorbingly_persistently.1).trans persistently_and_intuitionistically_sep_r.1
  refine h1.trans <| (sep_mono_l hprem).trans <| sep_assoc.1.trans <| sep_mono_r ?_
  exact (specialize_wand (p := true) .rfl emp_sep_rev).trans emp_sep.1

theorem specialize_dup_context [BI PROP] {P : PROP} {pa A P' pb B}
  (h : P ∗ □?pa A ⊢ P' ∗ □?pb B)
  (h2 : pa = true ∨ Affine A)
  [IntoPersistently pb B B']
  : P ∗ □?pa A ⊢ P ∗ □ B' := by
    apply Entails.trans _ persistently_and_intuitionistically_sep_r.1
    apply and_intro
    · cases h2 <;> subst_eqs <;> apply sep_elim_l
    · apply h.trans $ (sep_mono_r (persistentlyIf_of_intuitionisticallyIf.trans into_persistently)).trans sep_elim_r

public meta section
open Lean Elab Tactic Meta Qq Std

structure SpecializeState {prop : Q(Type u)} (bi : Q(BI $prop)) (orig : Q($prop)) where
  (e : Q($prop)) (hyps : Hyps bi e) (p : Q(Bool)) (out : Q($prop))
  pf : Q($orig ⊢ $e ∗ □?$p $out)

private def SpecializeState.collectGoalUniqs
    (self : @SpecializeState u prop bi orig) (ns : List Ident) : ProofModeM NameSet := do
  ns.foldlM (init := ({} : NameSet)) fun uniqs name =>
    return uniqs.insert (← self.hyps.findWithInfo name)

private def SpecializeState.processWandIdent
    (self : @SpecializeState u prop bi orig)
    (i : Ident) : ProofModeM (SpecializeState bi orig) := do
  let { hyps, p, out, pf, .. } := self
  let uniq ← hyps.findWithInfo i
  let ⟨e', hyps', out₁, out₁', p1, _, pf'⟩ := hyps.remove false uniq
  let p2 := if isTrue p1 then p else q(false)
  have : $out₁ =Q iprop(□?$p1 $out₁') := ⟨⟩
  have : $p2 =Q ($p1 && $p) := ⟨⟩
  let out₂ ← mkFreshExprMVarQ prop
  let some _ ← ProofModeM.trySynthInstanceQ q(IntoWand $p $p1 $out .in $out₁' .out $out₂) |
    throwError m!"ispecialize: cannot instantiate {out} with {out₁'}"
  let pf := q(specialize_wand $pf $pf')
  return { e := e', hyps := hyps', p := p2, out := out₂, pf }

private def SpecializeState.processWandPure
    (self : @SpecializeState u prop bi orig)
    (t : Term) : ProofModeM (SpecializeState bi orig) := do
  let { e, hyps, p, out, pf, .. } := self
  let v ← mkFreshLevelMVar
  let α : Q(Sort v) ← mkFreshExprMVarQ q(Sort v)
  let Φ : Q($α → $prop) ← mkFreshExprMVarQ q($α → $prop)
  let some _ ← ProofModeM.trySynthInstanceQ q(IntoForall $out $Φ)
    | throwError "ispecialize: {out} is not a lean premise"
  let x ← elabTermEnsuringTypeQ (u := .succ .zero) t α
  have out' : Q($prop) := Expr.headBeta q($Φ $x)
  have : $out' =Q $Φ $x := ⟨⟩
  let newMVarIds ← getMVarsNoDelayed x
  for mvar in newMVarIds do addMVarGoal mvar
  return { e, hyps, p, out := out', pf := q(specialize_forall $pf $x) }

private def SpecializeState.processWandGoalSpatial
    (self : @SpecializeState u prop bi orig)
    (neg : Bool) (ns : List Ident) (g : Name)
    : ProofModeM (SpecializeState bi orig) := do
  let { e, hyps, p, out, pf, .. } := self
  let uniqs ← self.collectGoalUniqs ns
  let ⟨el, _, hypsl, hypsr, h⟩ := hyps.split bi (λ _ uniq => Bool.xor neg (uniqs.contains uniq))
  let out₁ ← mkFreshExprMVarQ prop
  let out₂ ← mkFreshExprMVarQ prop
  let some hwand ← ProofModeM.trySynthInstanceQ q(IntoWand $p false $out .out $out₁ .out $out₂) |
    throwError m!"ispecialize: {out} is not a wand"
  let pf' ← addBIGoal hypsr out₁ g
  let pfSpatial := q(specialize_subgoal (q := $p) $pf $h $pf' (inst := $hwand))
  match matchBool p with
  | .inl _ =>
    let some _ ← ProofModeM.trySynthInstanceQ q(BIPositive $prop)
      | return { e := el, hyps := hypsl, p := q(false), out := out₂, pf := pfSpatial }
    let some _ ← ProofModeM.trySynthInstanceQ q(Intuitionistic iprop($e ∗ □ $out))
      | return { e := el, hyps := hypsl, p := q(false), out := out₂, pf := pfSpatial }
    let pfIntuitionistic := q(specialize_subgoal_intuitionistic .rfl $h $pf' (inst := $hwand))
    let pf := q($(pf).trans $pfIntuitionistic)
    return { e := el, hyps := hypsl, p := q(true), out := out₂, pf }
  | .inr _ =>
    return { e := el, hyps := hypsl, p := q(false), out := out₂, pf := pfSpatial }


private def SpecializeState.processWandGoalModal
    (self : @SpecializeState u prop bi orig)
    (neg : Bool) (ns : List Ident) (g : Name)
    : ProofModeM (SpecializeState bi orig) := do
  let { hyps, p, out, pf, .. } := self
  let uniqs ← self.collectGoalUniqs ns
  let ⟨el, _, hypsl, hypsr, h⟩ := hyps.split bi (λ _ uniq => Bool.xor neg (uniqs.contains uniq))
  let out₁ ← mkFreshExprMVarQ prop
  let out₁' ← mkFreshExprMVarQ prop
  let out₂ ← mkFreshExprMVarQ prop
  let some hwand ← ProofModeM.trySynthInstanceQ q(IntoWand $p false $out .out $out₁ .out $out₂)
    | throwError m!"ispecialize: {out} is not a wand"
  let some hmod ← ProofModeM.trySynthInstanceQ q(AddModal $out₁' $out₁ $out₂)
    | throwError m!"ispecialize: cannot generate a specialization subgoal for {out}"
  let pf' ← addBIGoal hypsr out₁' g
  let pf := q(specialize_subgoal_modal (q := $p) $pf $h $pf' (inst := $hwand) (hmod := $hmod))
  return { e := el, hyps := hypsl, p := q(false), out := out₂, pf }

private def SpecializeState.processWandGoalIntuitionistic
    (self : @SpecializeState u prop bi orig) (g : Name)
    : ProofModeM (SpecializeState bi orig) := do
  let { e, hyps, p, out, pf, .. } := self
  let out₁ ← mkFreshExprMVarQ prop
  let out₂ ← mkFreshExprMVarQ prop
  let some _ ← ProofModeM.trySynthInstanceQ q(IntoWand $p true $out .out $out₁ .out $out₂)
    | throwError m!"ispecialize: {out} does not have a persistent premise"
  let some hpers ← ProofModeM.trySynthInstanceQ q(Persistent $out₁)
    | throwError m!"ispecialize: persistent specialization requires a persistent premise"
  let some hwand ← ProofModeM.trySynthInstanceQ q(IntoWand $p true $out .in $out₁ .out $out₂)
    | throwError m!"ispecialize: {out} does not have a persistent premise"
  let some habs ← ProofModeM.trySynthInstanceQ q(IntoAbsorbingly iprop(<absorb> $out₁) $out₁)
    | throwError m!"ispecialize: cannot generate a persistent specialization subgoal for {out}"
  let pf' ← addBIGoal hyps q(iprop(<absorb> $out₁)) g
  let pf := q(
    let _ : Persistent $out₁ := $hpers
    let _ : IntoAbsorbingly iprop(<absorb> $out₁) $out₁ := $habs
    specialize_subgoal_persistent (q := $p) $pf $pf' (inst := $hwand))
  return { e, hyps, p, out := out₂, pf }

/-- `iCasesPat.should_try_dup_context` determines when iSpecializeCore should try to duplicate the separation context.
The duplication only works if the conclusion of the specialization is persistent.
-/
def iCasesPat.should_try_dup_context (pat : iCasesPat) : Bool :=
  match pat with
  | .intuitionistic _ => true
  | .pure _ => true
  | _ => false

/-- Specialize a proposition `A` by applying a sequence of specialization patterns.

## Parameters
- `hyps`: Current proof mode hypothesis context
- `pa`: Persistence flag for `A`
- `spats`: List of specialization patterns to apply sequentially
- `try_dup_context`: Boolean whether specialize should try to duplicate the context. See [iCasesPat.should_try_dup_context]

## Returns
A tuple containing:
- `e`: Proposition for `hyps'`
- `hyps'`: Updated hypothesis context, =`hyps` if context duplication succeeds
- `pb`: Persistence flag for `B`, =`true` if context duplication succeeds
- `B`: Resulting proposition after applying all patterns
- `pf`: Proof of `hyps ∗ □?pa A ⊢ hyps' ∗ □?pb B`, =`hyps ∗ □?pa A ⊢ hyps ∗ □ B` if context duplication succeeds
-/
def iSpecializeCore {e} (hyps : @Hyps u prop bi e) (pa : Q(Bool)) (A : Q($prop)) (spats : List SpecPat) (try_dup_context : Bool := false) :
  ProofModeM ((e' : _) × Hyps bi e' × (pb : Q(Bool)) × (B : Q($prop)) × Q($e ∗ □?$pa $A ⊢ $e' ∗ □?$pb $B)) := do
  let state : @SpecializeState u prop bi q(iprop($e ∗ □?$pa $A)) := { e, hyps, out := A, p := pa, pf := q(.rfl) }
  let ⟨_, hyps', pb, B, pf⟩ ← spats.foldlM (init := state) fun st pat =>
    match pat with
    | .ident i => st.processWandIdent i
    | .pure t => st.processWandPure t
    | .goal kind neg ns g =>
      match kind with
      | .spatial => st.processWandGoalSpatial neg ns g
      | .modal => st.processWandGoalModal neg ns g
      | .intuitionistic => st.processWandGoalIntuitionistic g

  if try_dup_context && !spats.any SpecPat.isModal then
    -- context duplication succeeds if `B` is persistent, and `A` is persistent or affine
    let B' : Q($prop) ← mkFreshExprMVarQ q($prop)
    let .some _ ← trySynthInstanceQ q(IntoPersistently $pb $B $B')
      | return ⟨_, hyps', pb, B, pf⟩
    have af : MetaM (Option Q($pa = true ∨ Affine $A)) :=
      match matchBool pa with
      | .inl _ => return some q(.inl (.refl _))
      | .inr _ => do
        let .some h ← trySynthInstanceQ q(Affine $A) | return none
        return some q(.inr $h)
    let some af ← af | return ⟨_, hyps', pb, B, pf⟩
    return ⟨_, hyps, q(true), B', q(specialize_dup_context $pf $af)⟩
  return ⟨_, hyps', pb, B, pf⟩

elab "ispecialize" colGt pmt:pmTerm : tactic => do
  let pmt ← liftMacroM <| PMTerm.parse pmt
  ProofModeM.runTactic λ mvar { bi, hyps, goal, .. } => do
  -- hypothesis must be in the context, otherwise use ihave
  let name := ⟨pmt.term⟩
  let some uniq ← try? <| hyps.findWithInfo name
    | throwError "{name} should be a hypothesis, use ihave instead"
  let some ⟨name, _, hyps', _, out, p, _, pf⟩ := Id.run <|
    hyps.removeG true λ name uniq' _ _ => if uniq == uniq' then some name else none
    | throwError "ispecialize: cannot find argument"

  let ⟨_, hyps'', pb, B, pf'⟩ ← iSpecializeCore hyps' p out pmt.spats
  let hyps''' := Hyps.add bi name uniq pb B hyps''
  let pf'' ← addBIGoal hyps''' goal
  mvar.assign q(($pf).1.trans <| $(pf').trans <| $pf'')
