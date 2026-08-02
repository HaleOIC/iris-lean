# Synthetic Resource-Conflict Benchmark Framework

Status: generator and runner schema version 2.

## Evaluation purpose

The synthetic benchmark isolates the resource-allocation problem at the center of `iaesop`'s search-settle-replay architecture. It complements the hand-written HeapLang, IrisITree, and proof-coverage tests: those establish practical usefulness, while this family directly evaluates robustness against premature resource choices and presentation order.

The intended research questions are:

1. How does search scale as the number of resource-target pairs increases?
2. How does it degrade as the density of locally valid decoy assignments increases?
3. Is success and search cost stable under independent changes to hypothesis, target, and rule order?
4. Which search, settlement, and replay mechanisms account for that behavior?

## Triangular resource-allocation family

For `k` spatial resources `R0, ..., R(k-1)` and target leaves `T0, ..., T(k-1)`, the canonical rules are:

```text
Ri |- Ti
```

A conflict rule has the form:

```text
Rj |- Ti, where j > i
```

The generated goal is:

```text
R0 * ... * R(k-1) |- T0 * ... * T(k-1)
```

Every conflict is locally relevant because it concludes a real target leaf. Globally it steals the canonical resource of a later target.

The family has two invariants:

- The canonical assignment always proves the goal.
- The canonical assignment is the unique complete resource assignment.

Uniqueness follows by reverse induction. The final target can only use its canonical resource. After removing that pair, the preceding target can only use its canonical resource, and so on. Requiring every decoy edge to satisfy `j > i` prevents several conflicts from forming an alternative resource permutation.

## Size and ambiguity parameters

`propositions` counts all distinct atomic Iris proposition symbols. Even counts provide one resource and one target per pair. For odd counts, the final proposition is used as an intermediate on the first canonical path so that no declared proposition is unused.

For `k = floor(propositions / 2)` resource-target pairs, the maximum number of conflicts is:

```text
maximumConflicts = k * (k - 1) / 2
```

Absolute conflict counts are useful for reproducing a particular case. Cross-size experiments should use conflict density:

```text
conflictDensity = conflicts / maximumConflicts
```

The public interfaces accept either an exact conflict count or one requested density. Density is converted to the nearest integer conflict count. Metadata records both requested and realized density because small instances cannot represent every percentage exactly.

Recommended density levels are 0, 0.25, 0.5, 0.75, and 1.

## Independent presentation dimensions

The generator keeps three order dimensions independent so an experiment can attribute sensitivity correctly.

### Source order

- `canonical`: resource indices increase from left to right.
- `reversed`: resource indices decrease from left to right.
- `random`: a deterministic permutation derived from the presentation seed.

### Target order

- `canonical`: target indices increase from left to right.
- `constrained-first`: leaves with fewer applicable conflicts appear first.
- `flexible-first`: leaves with more applicable conflicts appear first.
- `random`: a deterministic permutation derived from the presentation seed.

At full density, canonical target order and flexible-first order coincide for the triangular family. Experiments should include constrained-first when they need the opposite ordering.

### Rule order

- `canonical-first`: canonical rules precede conflicts for each target.
- `conflict-first`: conflicts precede canonical rules for each target.
- `random`: a deterministic permutation derived from the presentation seed.

The legacy `canonical`, `adversarial`, and `random` variants remain compatibility presets. Paper experiments should use the independent dimensions.

## Seeds and sampling

The master seed, proposition count, and logical sample index determine one stable ordering of all valid conflict edges. The realized conflict count selects a prefix of that ordering. Therefore, for a fixed size and sample, every lower-density conflict set is a subset of every higher-density set. Presentation modes and the order-sample index determine a separate presentation seed.

Consequently:

- changing `sample` produces another logical conflict graph;
- changing `order-sample` preserves the logical instance but produces another random presentation;
- changing one deterministic order mode leaves the other two dimensions untouched;
- all concrete seeds and realized orders are recorded in metadata.

For order-robustness experiments, generate 20 to 50 random order samples per logical instance and report median, interquartile range, extrema, and timeout rate.

## Suggested controlled experiments

| Experiment | Source order | Target order | Rule order |
| --- | --- | --- | --- |
| Baseline | canonical | canonical | canonical-first |
| Hypothesis sensitivity | reversed | canonical | canonical-first |
| Goal sensitivity | canonical | constrained-first or flexible-first | canonical-first |
| Rule sensitivity | canonical | canonical | conflict-first |
| Combined adversarial | reversed | flexible-first | conflict-first |
| Random robustness | random | random | random |

Do not treat the combined adversarial configuration as evidence about any one ordering dimension. Its role is only to provide a deliberately difficult combined presentation.

## Correctness and reproducibility contract

Before rendering Lean, the generator verifies:

- exact proposition and conflict counts;
- every proposition is used;
- conflict edges are distinct and strictly triangular;
- source, target, and rule presentations are permutations;
- a density request realizes the recorded conflict count;
- the canonical witness does not reuse a spatial resource.

Structural tests independently enumerate small resource assignments and confirm that maximal triangular conflict graphs have exactly one complete assignment. Generated theorems are accepted only after Lean elaboration and kernel checking.

Case metadata records the generator schema, RNG algorithm, seeds, conflict graph, density, presentation modes and realized orders, search strategy, and logical and presentation identifiers. Runner results additionally record the Git commit, Lean version, machine information, timeout, process wall time, status, and kernel-check result.

## Measurement boundary

The current runner measures fresh Lean-process wall time. This includes startup and file elaboration, so it is not tactic-only timing.

The next instrumentation change should expose:

- expanded search states;
- failed branches and backtracking events;
- copied platforms;
- fabricated and inherited goals;
- maximum frontier size;
- settlement attempts, retries, and failures;
- search, settlement, and replay time;
- replay success and total runtime.

Those counters belong in `Iris.ProofMode.Aesop`, not in the formula generator. Trace-based approximations should not be mixed with normal timing runs because tracing changes runtime substantially.

## Scope

Version 2 implements the triangular `split` family. Case-duplication and nested mixed-platform families, eager-splitting or no-reconsideration baselines, and tactic-internal phase instrumentation remain future work.
