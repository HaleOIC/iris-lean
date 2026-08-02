# Synthetic `iaesop` benchmarks

This directory contains the first implementation of the framework described in [`../BENCHMARK_FRAMEWORK.md`](../BENCHMARK_FRAMEWORK.md). It generates provable separation-logic entailments with controlled resource conflicts and runs them in isolated Lean processes.

## Conflict construction

For each target leaf `Qi`, the canonical rule consumes resource `Ri`. A conflict for `Qi` consumes a later resource `Rj`, where `j > i`, while producing the same `Qi`. The decoy is therefore locally relevant but steals the only canonical resource for target `Qj`.

Restricting all decoys to `j > i` makes the resource-to-target graph triangular. The last target must use its canonical resource, then the preceding target must use its canonical resource, and so on. Thus multiple decoys cannot combine into a second successful resource permutation.

The generator distributes decoys across targets before placing several on the same target. With `k = propositions / 2` resource-target pairs, the maximum supported conflict count is `k * (k - 1) / 2`.

## Generate one case

From the `IAesopTest` package directory:

```text
python3 benchmarks/generate.py \
  --seed 42 \
  --propositions 20 \
  --density 50% \
  --source-order reversed \
  --target-order flexible-first \
  --rule-order conflict-first \
  --output /tmp/iaesop-case.lean \
  --metadata-output /tmp/iaesop-case.json
```

Use `--seed auto` to choose a 64-bit seed from system entropy. The chosen concrete seed is printed and embedded in the generated metadata. Published and checked-in cases should use concrete seeds.

Absolute conflict counts remain available through `--conflicts`. Density is preferable when comparing different sizes:

```text
density = selected conflicts / maximum conflicts
maximum conflicts = k * (k - 1) / 2
```

Because conflicts are discrete, the generator records both the requested density and the realized density after rounding to the nearest conflict count.

For a fixed seed, proposition count, and logical sample, density levels are monotone: a lower-density conflict set is a prefix and subset of every higher-density set. Density experiments therefore add ambiguity without replacing earlier decoys.

The three presentation dimensions are independent:

- `--source-order canonical|reversed|random` controls spatial hypothesis order;
- `--target-order canonical|constrained-first|flexible-first|random` controls target-conjunct order;
- `--rule-order canonical-first|conflict-first|random` controls applicable-rule order.

`constrained-first` places targets with fewer decoys first. `flexible-first` places targets with more decoys first, delaying discovery that a stolen resource was needed by a constrained target.

The older `--variant` option remains as a compatibility preset:

- `canonical`: canonical rules precede conflicting rules;
- `adversarial`: conflicts precede the corresponding canonical rules, resources are reversed, and conflict-heavy targets come first;
- `random`: all three dimensions are permuted from a derived presentation seed.

Do not use presets for order-sensitivity attribution. Change one independent dimension at a time instead. Use `--order-sample N` to select another deterministic random presentation of the same logical instance.

Pass `--trace` to a single-case generation command when inspecting search behavior. It enables the existing `iaesop.search.expand` trace in the generated Lean input.

## Run a benchmark grid

```text
python3 benchmarks/run.py \
  --seed 42 \
  --propositions 10,20,30 \
  --densities 0,0.25,0.5,0.75,1 \
  --samples 5 \
  --source-orders canonical \
  --target-orders canonical \
  --rule-orders canonical-first \
  --strategies bestFirst depthFirst breadthFirst \
  --timeout 120 \
  --results benchmarks/results/example.jsonl
```

To isolate each order dimension, run controlled configurations rather than one combined grid:

| Experiment | Source order | Target order | Rule order |
| --- | --- | --- | --- |
| Baseline | `canonical` | `canonical` | `canonical-first` |
| Hypothesis sensitivity | `reversed` | `canonical` | `canonical-first` |
| Goal sensitivity | `canonical` | `flexible-first` or `constrained-first` | `canonical-first` |
| Rule sensitivity | `canonical` | `canonical` | `conflict-first` |
| Combined adversarial | `reversed` | `flexible-first` | `conflict-first` |
| Random robustness | `random` | `random` | `random` |

For random robustness, add `--order-samples 20` or more. The logical instance and its conflict graph stay fixed while each order sample receives a separately derived presentation seed.

The runner performs one unmeasured warm-up by default, invokes a fresh Lean process for each observation, and writes one JSON object per line. Its current `processWallTimeMs` measurement includes Lean startup and file elaboration. It must not yet be interpreted as tactic-only time; tactic phase counters described in the framework document remain future instrumentation work.

A nonzero exit status means at least one measured case failed or timed out. Failure rows retain a short diagnostic tail, while full generated inputs can be retained with `--keep-inputs DIR`.

## Quick checks

```text
PYTHONPYCACHEPREFIX=/tmp/iaesop-pycache python3 -m py_compile \
  benchmarks/generate.py benchmarks/run.py \
  benchmarks/test_generate.py benchmarks/test_run.py

PYTHONPYCACHEPREFIX=/tmp/iaesop-pycache python3 -m unittest \
  discover -s benchmarks -p 'test_*.py'

python3 benchmarks/run.py \
  --seed 20260802 \
  --propositions 4,6 \
  --densities 0,0.5,1 \
  --samples 1 \
  --source-orders canonical reversed \
  --target-orders canonical \
  --rule-orders canonical-first \
  --timeout 10 \
  --results /tmp/iaesop-smoke.jsonl
```
