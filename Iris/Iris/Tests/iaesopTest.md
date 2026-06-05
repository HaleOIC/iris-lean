# `iaesop` tactic testing coverage

## Basic

### `Iris/Tests/Test0Trivial.lean`

| theorem name | successfully covered | missing |
| --- | --- | --- |
| `example@12` | Yes | Covered by default `iaesop`; not specifically baseline. |
| `example@15` | Yes | Covered by `iaesop bestFirst`; not specifically baseline. |
| `example@18` | Yes | Covered by `iaesop depthFirst`; not specifically baseline. |
| `example@21` | Yes | Covered by `iaesop breadthFirst`; not specifically baseline. |
| `example@24` | Yes | Covered by `iaesop simp`; not specifically baseline. |
| `example@27` | Yes | Covered by `iaesop depthFirst unfold`; not specifically baseline. |
| `example@30` | Yes | Covered by `iaesop breadthFirst normAll`; not specifically baseline. |
| `example@33` | Yes | Covered by default `iaesop`; commented baseline remains untested. |
| `example@38` | Yes | Nothing; basic spatial context split is covered. |
| `example@42` | Yes | Nothing; multiple affine context split is covered. |
| `example@46` | Yes | Nothing; wand chaining and affine split are covered. |
| `example@51` | Yes | Nothing; nested wand/context split is covered. |
| `example@55` | Yes | Nothing; wand generation from unused spatial premise is covered. |
| `example@61` | Yes | Nothing; registered `forward 100% backward 100%` theorem application is covered. |
| `example@67` | Yes | Nothing; named pure/spatial specialization is covered. |
| `example@74` | Yes | Nothing; mixed forall and wand specialization is covered. |
| `example@79` | Yes | Nothing; Lean hypothesis application through `applyHyps` is covered. |
| `example@84` | Yes | Nothing; forall specialization from Iris hypothesis is covered. |
| `example@89` | Yes | Nothing; context refill after forall specialization is covered. |
| `example@94` | Yes | Nothing; fupd exact/introduction path is covered. |
| `example@99` | Yes | Nothing; intuitionistic forall from Lean hypothesis is covered. |
| `example@102` | Yes | Nothing; nested bupd idempotence shape is covered. |
| `example@105` | Yes | Nothing; disjunction case split plus affine frame is covered. |
| `example@109` | Yes | Nothing; intuitionistic conjunction projection under forall is covered. |
| `example@114` | Yes | Nothing; existential introduction with anonymous metavariable is covered. |
| `example@117` | Yes | Nothing; existential introduction from spatial hypothesis is covered. |

`Iris/Tests/Test1BupdPlain.lean`

| theorem name | successfully covered | missing |
| --- | --- | --- |
| `BUpdPlain_ne` | No | Hand-written `NonExpansive`; no `iaesop` call. |
| `BUpdPlain_intro` | Yes | Nothing. |
| `BUpdPlain_mono` | Yes | Nothing. |
| `BUpdPlain_idemp` | Yes | Nothing. |
| `BUpdPlain_frame_r` | Yes | Nothing. |
| `BUpdPlain_plainly` | Yes | Nothing. |
| `BUpd_BUpdPlain` | Yes | Nothing. |
| `own_updateP` | Yes | Nothing. |

### `Iris/Tests/Test2FixedPoint.lean`

1. Registering `mono_pred` is not currently supported because it is an internal theorem of the class.
    - Not sure whether registering it, since $\Psi$ and $\Phi$ always need to be specified
    - Another solution is use `ihave` to inject some hypothesis before search (see `wf_pred_mono`)
2. The definition only works in one direction. During the search stage, if we obtain `∀ Φ, (□ ∀ x, F Φ.f x -∗ Φ.f x) -∗ Φ.f z`, we cannot convert it back into `bi_least_fixpoint z`. (in `least_fixpoint_unfold_1`)
3. The type of applied hypothesis is `∗HF : ∀ Φ, (□ ∀ x, F Φ.f x -∗ Φ.f x) -∗ Φ.f x`, and we can not align `Φ.f x` with `Φ x`. (in `least_fixpoint_iter`)
    - This seems to be solvable? (after expansion, `HF` will become `?Φ.f x`)
4. Normalization stage's quantifier elimintation is eager, making it impossible to detect the presence of `least_fixpoint_iter`'s conclusion `∀ x, bi_least_fixpoint F x -∗ Φ x` (in `least_fixpoint_affine`, `laest_fixpoint_strong_mono`, `least_fixpoint_ind_wf`)
    - Before normalization stage, we try to expand the goal directly? it requires backward theorem registration procedure do not peel (`∀`) eagerly. **(Important!)**
    - However, there exists a counterexample (see `least_fixpoint_ind`)
5. Require external theorem (in `least_fixpoint_absorbing`, `least_fixpoint_persistent_affine`)
6. Unfolding this theorem will likely require forward reasoning; (see `greatest_fixpoint_paco`).

| theorem name | successfully covered | missing |
| --- | --- | --- |
| `bi_least_fixpoint` NonExpansive instance | No | Pure nonexpansiveness proof is hand-written with `refine`; not a proof-mode goal. |
| `bi_greatest_fixpoint` NonExpansive instance | No | Pure nonexpansiveness proof is hand-written with `refine`; not a proof-mode goal. |
| `least_fixpoint_unfold_2` | Partial | Needs intros and `mono_pred`; baseline only closes generated subgoals. |
| `least_fixpoint_unfold_1` | Partial | Needs specialization and a `NonExpansive` instance; baseline closes the final subgoal. |
| `least_fixpoint_unfold` | No | Direct equivalence from the two unfold lemmas; no `iaesop` call. |
| `least_fixpoint_iter` | Partial | Needs specialization; baseline closes after `ispecialize`. |
| `least_fixpoint_affine` | Partial | Needs `revert` and `iapply least_fixpoint_iter`; baseline closes the affine body. |
| `least_fixpoint_absorbing` | Partial | Needs Loeb-style setup and `mono_pred`; baseline closes only branch subgoals. |
| `least_fixpoint_persistent_affine` | Partial | Needs persistent transform and `mono_pred`; baseline closes branches. |
| `least_fixpoint_persistent_absorbing` | Partial | Needs absorbing instance setup; baseline closes the final persistent proof. |
| `least_fixpoint_strong_mono` | Partial | Uses `least_fixpoint_iter` and `least_fixpoint_unfold`; no theorem-level baseline. |
| `wf_pred_mono` local instance | Partial | Baseline covers only the left conjunct case; the right case is outside baseline. |
| `least_fixpoint_ind_wf` | Partial | Needs hand-written helper `ihave`, monotonicity, and modality setup; baseline closes the final split. |
| `least_fixpoint_ind` | Partial | Needs monotonicity instance and strong-mono application; baseline closes the final pure branch. |
| `greatest_fixpoint_ne_outer` | No | Pure nonexpansiveness proof; no `iaesop` call. |
| `greatest_fixpoint_unfold_1` | Partial | Needs `NonExpansive`, destructuring, and `mono_pred`; baseline closes subgoals. |
| `greatest_fixpoint_unfold_2` | Partial | Needs existential witness and split; baseline closes inner goals. |
| `greatest_fixpoint_unfold` | No | Direct equivalence from the unfold lemmas; no `iaesop` call. |
| `greatest_fixpoint_coiter` | Partial | Needs intros and witness; baseline closes split. |
| `greatest_fixpoint_absorbing` | Partial | Needs coiteration and `ihave`; baseline closes local branches. |
| `greatest_fixpoint_strong_mono` | Yes | Nothing. |
| `paco_mono` local instance | Partial | Baseline covers the left disjunct case; the right disjunct is outside baseline. |
| `greatest_fixpoint_paco` | Partial | Needs coinduction setup and case extraction; baseline closes a disjunction branch. |
| `greatest_fixpoint_coind` | Partial | Needs nonexpansive instances and paco setup; baseline closes several branch goals. |

Iris/Tests/Test3Proofs.lean

| theorem name | successfully covered | missing |
| --- | --- | --- |
| `proof_example_1` | Yes | Nothing; the whole example is covered by baseline. |

Iris/Tests/Test4Fupd.lean

| theorem name | successfully covered | missing |
| --- | --- | --- |
| `uPred_fupd` NonExpansive instance | No | Hand-written nonexpansiveness proof. |
| `uPred_fupd_instance` | No | Direct instance assignment. |
| `uPred_bi_fupd` | Partial | Needs mask rewrites, resource splitting, and specializations; baseline closes several law subgoals. |
| `BIUpdateFUpdate` instance for `uPred_fupd` | Yes | Nothing. |
| `uPred_bi_fupd_plainly_no_lc` | Partial | Needs fupd/plainly extraction; baseline closes resulting goals. |
| `lc_fupd_elim_later` | Yes | Nothing. |
| `lc_fupd_add_later` | Partial | Needs intros and delayed `ihave`; baseline closes generated goals. |
| `lc_fupd_add_laterN` | No | Induction proof remains outside baseline; the commented baseline in the successor case is unused. |
| `fupd_soundness_lc` | No | TODO mentions metavariables; commented baseline is unused. |
| `fupd_soundness_no_lc` | No | TODO mentions metavariables; commented baseline is unused. |
| `fupd_soundness_gen` | No | Case split plus direct applications; commented baseline is unused. |
| `step_fupdN_soundness_no_lc` | Partial | Needs soundness reduction, mask/plainly setup, and modal steps; baseline closes the final later goal. |
| `step_fupdN_soundness_lc` | Partial | TODO mentions possible timeout/loop; baseline covers only the zero case, successor remains outside baseline. |
| `step_fupdN_soundness_gen` | No | Case split plus direct applications; commented baseline is unused. |
| `step_fupdN_soundness_no_lc'` | Partial | Needs case split and induction; baseline closes one successor induction branch. |
| `step_fupdN_soundness_lc'` | Partial | Needs split/induction and resource handling; baseline closes zero and successor tails. |

Iris/Tests/Test5Invariants.lean

| theorem name | successfully covered | missing |
| --- | --- | --- |
| `inv_contractive` | No | Hand-written contractiveness proof. |
| `inv_ne` | No | Direct `ne_of_contractive`. |
| `inv_persistent` | No | Uses `infer_instance`, not iaesop. |
| `own_inv_persistent` | No | Uses `infer_instance`, not iaesop. |
| `except_0_inv` | Yes | Nothing. |
| `is_except_0_inv` | Yes | Baseline covers the instance field. |
| `own_inv_acc` | Partial | Needs substantial hand proof: set equalities, ownE splits, and `ownI_open/close`; baseline closes recombination subgoals. |
| `own_inv_alloc` | Partial | Needs allocation/update and freshness proof; baseline closes proof-mode side goals. |
| `own_inv_alloc_open` | Partial | Needs freshness, set equalities, ownE splits, and close continuation; baseline closes recombination subgoals. |
| `own_inv_to_inv` | No | TODO remains; baseline is commented out. |
| `inv_alloc` | Partial | Needs `own_inv_alloc`; baseline closes conversion to `inv`. |
| `inv_alloc_open` | Partial | Needs `own_inv_alloc_open`; baseline closes final split. |
| `inv_acc` | Yes | Nothing. |
| `inv_acc_strong` | Partial | Needs mask-frame manipulation and rewrites; baseline closes the tail. |
| `inv_acc_timeless` | Partial | Needs `inv_acc` and timeless elimination; baseline closes the tail. |
| `inv_alter` | Partial | Needs invariant opening and `HPQ`; baseline closes final split/close. |
| `inv_iff` | Yes | Nothing; the whole theorem is covered by baseline. |
| `inv_combine` | Partial | Needs subset/disjoint pure reasoning and mask close; baseline closes the final modal tail. |
| `inv_combine_dup_l` | Partial | Needs duplicate splitting; baseline closes the rest after `HI1`. |
| `inv_split_l` | Yes | Nothing; the whole theorem is covered by baseline. |
| `inv_split_r` | Yes | Nothing; the whole theorem is covered by baseline. |
| `inv_split` | Yes | Nothing; the whole theorem is covered by baseline. |

Iris/Tests/Test6LaterCredits.lean

| theorem name | successfully covered | missing |
| --- | --- | --- |
| `lc_split` | No | Direct equivalence proof; comment notes timeout on `iOwn_op`. |
| `lc_zero` | No | Direct `iOwn_unit`. |
| `lc_supply_bound` | No | Registered backward, but proof needs resource validity reasoning. |
| `lc_decrease_supply` | No | Registered backward, but proof needs update/resource reasoning. |
| `lc_succ` | No | Direct rewrite plus `lc_split`. |
| `lc_weaken` | No | Manual arithmetic decomposition and split. |
| `lc_timeless` | No | Uses `infer_instance`, not iaesop. |
| `lc_0_persistent` | No | Direct proof-mode instance application. |
| `from_sep_lc_add` | No | Direct proof-mode class instance field. |
| `from_sep_lc_S` | No | Direct proof-mode class instance field. |
| `into_sep_lc_add` | No | Direct proof-mode class instance field. |
| `into_sep_lc_S` | No | Direct proof-mode class instance field. |
| `le_upd_pre` Contractive instance | No | Hand-written contractiveness proof. |
| `le_upd_unfold` | No | Direct fixpoint unfold equivalence. |
| `le_upd` NonExpansive instance | No | Hand-written well-founded nonexpansiveness proof. |
| `bupd_le_upd` | Partial | Needs `iintro` and `iapply le_upd_unfold`; baseline closes the body. |
| `le_upd_intro` | Yes | Nothing; the whole theorem is covered by baseline. |
| `le_upd_bind` | Partial | Needs Loeb and nested modal case analysis; baseline closes branches. |
| `le_upd_later_elim` | Partial | Needs credit bound arithmetic and supply update; baseline closes final existential branch. |
| `le_upd_mono` | Yes | Nothing; the whole theorem is covered by baseline. |
| `le_upd_trans` | Yes | Nothing; the whole theorem is covered by baseline. |
| `le_upd_frame_r` | Yes | Nothing; the whole theorem is covered by baseline. |
| `le_upd_frame_l` | Yes | Nothing; the whole theorem is covered by baseline. |
| `le_upd_later` | Partial | Needs credit intro and `le_upd_later_elim`; baseline closes later/introduction. |
| `except_0_le_upd` | Partial | TODO says slow; needs case split; baseline closes cases. |
| `le_upd_elim` | Partial | Needs well-founded induction, arithmetic, and iterated modal reasoning; baseline closes selected branches only. |
| `le_upd_elim_complete` | Partial | Needs `le_upd_elim`, repeat arithmetic, and modal mono; baseline closes two subgoals. |
| `elim_bupd_le_upd` | Partial | Needs `cases p`; baseline closes both instance cases. |
| `from_assumption_le_upd` | No | Direct transitive instance field; TODO nearby about instance theorem. |
| `from_pure_le_upd` | No | Case split and proof-mode steps; no baseline. |
| `is_except_0_le_upd` | Partial | Needs `except_0_le_upd`; baseline closes final mono. |
| `from_modal_le_upd` | Yes | Nothing. |
| `elim_modal_le_upd` | Partial | Needs `cases p`; baseline closes cases. |
| `frame_le_upd` | No | Direct `Frame` instance field. |
| `lc_alloc` | Partial | Needs `iOwn_alloc`, decomposition, and instance construction; baseline closes final split. |
| `lc_soundness` | Partial | Needs soundness reduction, allocation, iterated modal induction; baseline closes induction step tail. |
| `le_upd_if_ne` | No | Direct case split plus `infer_instance`. |
| `le_upd_if_mono` | Partial | Needs boolean case split; baseline closes each case. |
| `le_upd_if_intro` | Partial | Needs boolean case split; baseline closes each case. |
| `le_upd_if_bind` | Partial | Needs boolean case split; baseline closes each case. |
| `le_upd_if_trans` | Partial | Needs boolean case split; baseline closes each case. |
| `le_upd_if_frame_r` | Partial | Needs boolean case split; baseline closes each case. |
| `bupd_le_upd_if` | Partial | Needs boolean case split; baseline closes each case. |
| `le_upd_if_frame_l` | Partial | Needs boolean case split; baseline closes each case. |
| `except_0_le_upd_if` | Partial | Needs boolean case split; baseline closes each case. |
| `elim_bupd_le_upd_if` | No | Direct case split plus `infer_instance`. |
| `from_pure_le_upd_if` | No | Direct case split plus `infer_instance`. |
| `is_except_0_le_upd_if` | No | Direct case split plus `infer_instance`. |
| `from_modal_le_upd_if` | No | Direct case split plus `infer_instance`. |
| `elim_modal_le_upd_if` | No | Direct case split plus `infer_instance`. |
| `frame_le_upd_if` | No | Direct `Frame` instance field. |
| `from_assumption_le_upd_if` | No | Direct transitive instance field. |

Iris/Tests/Test7NaInvariants.lean

| theorem name | successfully covered | missing |
| --- | --- | --- |
| `instNaInvF_discreteE` | No | Direct discrete instance. |
| `coreId_valid_empty_empty` | No | Direct `rfl`. |
| `isUnit_valid_empty_empty` | No | Direct instance fields. |
| `instTimeless_own` | No | Uses `infer_instance`, not iaesop. |
| `instContractive_inv` | No | Hand-written contractiveness proof. |
| `instNonExpansive_inv` | No | Direct `ne_of_contractive`. |
| `instPersistentInv` | No | Uses `infer_instance`, not iaesop. |
| `instPersistent_own` | No | Uses `infer_instance`, not iaesop. |
| `NonAtomicInvariant.inv_iff` | Partial | TODO says acceleration issue; needs witness and invariant rewrite; baseline closes final equivalence branch. |
| `NonAtomicInvariant.alloc` | No | Direct `iOwn_alloc`. |
| `NonAtomicInvariant.own_disjoint` | No | Registered backward, but proof needs resource validity reasoning. |
| `NonAtomicInvariant.own_union` | No | Registered backward, but proof is direct equivalence/rewrite. |
| `NonAtomicInvariant.own_acc` | Partial | Needs set rewrite and union split; baseline closes final split. |
| `NonAtomicInvariant.own_empty` | No | Direct `iOwn_unit`. |
| `NonAtomicInvariant.inv_alloc` | Partial | Needs allocation/update and freshness proof; baseline closes generated proof-mode goals. |
| `NonAtomicInvariant.inv_acc` | Partial | Needs substantial invariant/token splitting and conflict reasoning; baseline closes several recombination/conflict subgoals. |

Iris/Tests/Test8Token.lean

| theorem name | successfully covered | missing |
| --- | --- | --- |
| `token_timeless` | No | Uses `infer_instance`, not iaesop. |
| `token_alloc_strong` | No | Allocation plus pure freshness proof. |
| `token_alloc` | No | Direct `iOwn_alloc`. |
| `token_exclusive` | No | Ownership validity proof. |

Iris/Tests/Test9WSat.lean

| theorem name | successfully covered | missing |
| --- | --- | --- |
| `ownI` Contractive instance | No | Hand-written nonexpansive/contractive proof. |
| `ownI` Persistent instance | No | Uses `infer_instance`, not iaesop. |
| `ownE_empty` | No | Direct `iOwn_unit`. |
| `ownE_op` | No | Registered backward, but proof is direct rewrite/equivalence. |
| `ownE_disjoint` | No | Registered backward, but proof needs resource validity reasoning. |
| `ownE_op_iff` | Partial | Needs constructor/destructuring; baseline derives disjointness subgoal. |
| `ownE_singleton_singleton` | No | Direct composition using `ownE_disjoint`. |
| `ownD_empty` | No | Registered backward, but proof is direct `iOwn_unit`. |
| `ownD_op` | No | Registered backward, but proof is direct rewrite/equivalence. |
| `ownD_disjoint` | No | Registered backward, but proof needs resource validity reasoning. |
| `ownD_op_iff` | Partial | Needs constructor/destructuring; baseline derives disjointness subgoal. |
| `ownD_singleton_twice` | No | Direct composition using `ownD_disjoint`. |
| `invariant_lookup` | No | Manual auth-fragment lookup and internal equality proof. |
| `ownI_open` | Partial | Needs lookup, big-sep deletion, and state update; baseline closes conflict case. |
| `ownI_close` | No | `wsat` close proof; no baseline. |
| `ownI_alloc` | No | Allocation/update, map equality, and big-sep insertion. |
| `ownI_alloc_open` | No | Allocation/update, continuation construction, and big-sep insertion. |
| `wsat_alloc` | No | Allocation of all three resources and empty map proof. |

### Waiting Feature

- [ ] register class level theorem
