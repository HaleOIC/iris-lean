#!/usr/bin/env python3
"""Generate deterministic synthetic resource-conflict benchmarks for iaesop."""

from __future__ import annotations

import argparse
import hashlib
import json
import random
import secrets
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence


SCHEMA_VERSION = 2
GENERATOR_VERSION = "2"
RNG_ALGORITHM = "Python random.Random (MT19937)"
VARIANTS = ("canonical", "adversarial", "random")
SOURCE_ORDERS = ("canonical", "reversed", "random")
TARGET_ORDERS = (
    "canonical",
    "constrained-first",
    "flexible-first",
    "random",
)
RULE_ORDERS = ("canonical-first", "conflict-first", "random")
VARIANT_PRESETS = {
    "canonical": ("canonical", "canonical", "canonical-first"),
    "adversarial": ("reversed", "flexible-first", "conflict-first"),
    "random": ("random", "random", "random"),
}
STRATEGIES = ("bestFirst", "depthFirst", "breadthFirst")
MAX_SEED = 2**64 - 1


class ConfigurationError(ValueError):
    """Raised when a requested benchmark cannot satisfy its contract."""


@dataclass(frozen=True, order=True)
class Conflict:
    """A decoy edge from a later resource to an earlier target."""

    resource: int
    target: int


@dataclass(frozen=True)
class Rule:
    name: str
    premise: int
    conclusion: int
    kind: str
    target_slot: int


@dataclass(frozen=True)
class BenchmarkCase:
    master_seed: int
    case_seed: int
    presentation_seed: int
    propositions: int
    requested_conflicts: int
    requested_density: float | None
    sample: int
    order_sample: int
    variant: str | None
    source_order_mode: str
    target_order_mode: str
    rule_order_mode: str
    strategy: str
    resources: tuple[int, ...]
    targets: tuple[int, ...]
    intermediate: int | None
    conflicts: tuple[Conflict, ...]
    source_order: tuple[int, ...]
    target_order: tuple[int, ...]
    rules: tuple[Rule, ...]
    rule_order: tuple[int, ...]
    logical_id: str
    case_id: str

    @property
    def proposition_names(self) -> tuple[str, ...]:
        return tuple(f"P{i}" for i in range(self.propositions))


def parse_seed(value: str) -> int:
    if value == "auto":
        return secrets.randbits(64)
    try:
        seed = int(value, 0)
    except ValueError as exc:
        raise ConfigurationError(
            f"seed must be 'auto' or an integer, got {value!r}"
        ) from exc
    if not 0 <= seed <= MAX_SEED:
        raise ConfigurationError(f"seed must be between 0 and {MAX_SEED}")
    return seed


def parse_density(value: str) -> float:
    original = value
    value = value.strip()
    try:
        if value.endswith("%"):
            density = float(value[:-1]) / 100.0
        else:
            density = float(value)
    except ValueError as exc:
        raise ConfigurationError(
            f"density must be a number between 0 and 1 or a percentage, got {original!r}"
        ) from exc
    if not 0.0 <= density <= 1.0:
        raise ConfigurationError(f"density must be between 0 and 1, got {density}")
    return density


def derive_seed(master_seed: int, *parts: object) -> int:
    payload = "\0".join(
        ["iaesop-synthetic-benchmark-v2", str(master_seed), *(str(p) for p in parts)]
    ).encode("utf-8")
    return int.from_bytes(hashlib.sha256(payload).digest()[:8], "big")


def maximum_conflicts(propositions: int) -> int:
    if propositions < 4:
        return 0
    pairs = propositions // 2
    return pairs * (pairs - 1) // 2


def conflicts_for_density(propositions: int, density: float) -> int:
    if not 0.0 <= density <= 1.0:
        raise ConfigurationError(f"density must be between 0 and 1, got {density}")
    maximum = maximum_conflicts(propositions)
    return int(maximum * density + 0.5)


def realized_density(propositions: int, conflicts: int) -> float:
    maximum = maximum_conflicts(propositions)
    return 0.0 if maximum == 0 else conflicts / maximum


def validate_configuration(propositions: int, conflicts: int, sample: int) -> None:
    if propositions < 4:
        raise ConfigurationError(
            "the split family requires at least 4 atomic propositions "
            "(two resources and two targets)"
        )
    if conflicts < 0:
        raise ConfigurationError("conflicts must be non-negative")
    maximum = maximum_conflicts(propositions)
    if conflicts > maximum:
        pairs = propositions // 2
        raise ConfigurationError(
            f"{propositions} propositions provide {pairs} resource-target pairs and "
            f"support at most {maximum} acyclic conflicts, got {conflicts}"
        )
    if sample < 0:
        raise ConfigurationError("sample must be non-negative")


def select_conflicts(pair_count: int, count: int, rng: random.Random) -> tuple[Conflict, ...]:
    """Select strict triangular edges, balanced across target leaves."""

    buckets: dict[int, list[int]] = {
        target: list(range(target + 1, pair_count))
        for target in range(pair_count - 1)
    }
    targets = list(buckets)
    rng.shuffle(targets)
    for resources in buckets.values():
        rng.shuffle(resources)

    selected: list[Conflict] = []
    while len(selected) < count:
        made_progress = False
        for target in targets:
            resources = buckets[target]
            if not resources:
                continue
            selected.append(Conflict(resource=resources.pop(), target=target))
            made_progress = True
            if len(selected) == count:
                break
        if not made_progress:
            raise AssertionError("validated conflict capacity was exhausted")
    return tuple(selected)


def canonical_rules(
    pair_count: int, targets: Sequence[int], intermediate: int | None
) -> list[Rule]:
    rules: list[Rule] = []
    for slot in range(pair_count):
        if slot == 0 and intermediate is not None:
            rules.append(
                Rule(
                    name="hCanon0Step0",
                    premise=0,
                    conclusion=intermediate,
                    kind="canonical",
                    target_slot=0,
                )
            )
            rules.append(
                Rule(
                    name="hCanon0Step1",
                    premise=intermediate,
                    conclusion=targets[0],
                    kind="canonical",
                    target_slot=0,
                )
            )
        else:
            rules.append(
                Rule(
                    name=f"hCanon{slot}",
                    premise=slot,
                    conclusion=targets[slot],
                    kind="canonical",
                    target_slot=slot,
                )
            )
    return rules


def conflict_rules(conflicts: Sequence[Conflict], targets: Sequence[int]) -> list[Rule]:
    return [
        Rule(
            name=f"hConflict{index}",
            premise=conflict.resource,
            conclusion=targets[conflict.target],
            kind="conflict",
            target_slot=conflict.target,
        )
        for index, conflict in enumerate(conflicts)
    ]


def presentation_orders(
    *,
    source_order_mode: str,
    target_order_mode: str,
    rule_order_mode: str,
    resources: Sequence[int],
    targets: Sequence[int],
    rules: Sequence[Rule],
    presentation_seed: int,
) -> tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...]]:
    source_order = list(resources)
    target_order = list(range(len(targets)))
    rule_order = list(range(len(rules)))

    source_rng = random.Random(derive_seed(presentation_seed, "source"))
    target_rng = random.Random(derive_seed(presentation_seed, "target"))
    rule_rng = random.Random(derive_seed(presentation_seed, "rule"))
    conflict_load = {
        target: sum(
            rule.kind == "conflict" and rule.target_slot == target for rule in rules
        )
        for target in target_order
    }

    if source_order_mode == "reversed":
        source_order.reverse()
    elif source_order_mode == "random":
        source_rng.shuffle(source_order)
    elif source_order_mode != "canonical":
        raise ConfigurationError(f"unknown source order {source_order_mode!r}")

    if target_order_mode == "constrained-first":
        target_order.sort(key=lambda target: (conflict_load[target], -target))
    elif target_order_mode == "flexible-first":
        target_order.sort(key=lambda target: (-conflict_load[target], target))
    elif target_order_mode == "random":
        target_rng.shuffle(target_order)
    elif target_order_mode != "canonical":
        raise ConfigurationError(f"unknown target order {target_order_mode!r}")

    if rule_order_mode == "canonical-first":
        rule_order.sort(
            key=lambda index: (
                rules[index].target_slot,
                rules[index].kind != "canonical",
                index,
            )
        )
    elif rule_order_mode == "conflict-first":
        rule_order.sort(
            key=lambda index: (
                rules[index].target_slot,
                rules[index].kind == "canonical",
                -rules[index].premise,
                index,
            )
        )
    elif rule_order_mode == "random":
        rule_rng.shuffle(rule_order)
    else:
        raise ConfigurationError(f"unknown rule order {rule_order_mode!r}")

    return tuple(source_order), tuple(target_order), tuple(rule_order)


def _digest(payload: object, length: int = 16) -> str:
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()[:length]


def build_case(
    *,
    master_seed: int,
    propositions: int,
    conflicts: int | None = None,
    density: float | None = None,
    sample: int = 0,
    order_sample: int = 0,
    source_order: str | None = None,
    target_order: str | None = None,
    rule_order: str | None = None,
    variant: str | None = None,
    strategy: str = "bestFirst",
) -> BenchmarkCase:
    if conflicts is not None and density is not None:
        raise ConfigurationError("specify either conflicts or density, not both")
    if density is not None:
        if not 0.0 <= density <= 1.0:
            raise ConfigurationError(f"density must be between 0 and 1, got {density}")
        requested_density = density
        conflicts = conflicts_for_density(propositions, density)
    else:
        requested_density = None
        conflicts = 0 if conflicts is None else conflicts

    validate_configuration(propositions, conflicts, sample)
    if order_sample < 0:
        raise ConfigurationError("order sample must be non-negative")
    if variant is not None:
        if variant not in VARIANTS:
            raise ConfigurationError(f"variant must be one of {', '.join(VARIANTS)}")
        if any(mode is not None for mode in (source_order, target_order, rule_order)):
            raise ConfigurationError(
                "variant presets cannot be combined with independent order controls"
            )
        source_order, target_order, rule_order = VARIANT_PRESETS[variant]
    else:
        source_order = source_order or "canonical"
        target_order = target_order or "canonical"
        rule_order = rule_order or "canonical-first"
    if source_order not in SOURCE_ORDERS:
        raise ConfigurationError(
            f"source order must be one of {', '.join(SOURCE_ORDERS)}"
        )
    if target_order not in TARGET_ORDERS:
        raise ConfigurationError(
            f"target order must be one of {', '.join(TARGET_ORDERS)}"
        )
    if rule_order not in RULE_ORDERS:
        raise ConfigurationError(f"rule order must be one of {', '.join(RULE_ORDERS)}")
    if strategy not in STRATEGIES:
        raise ConfigurationError(f"strategy must be one of {', '.join(STRATEGIES)}")

    pair_count = propositions // 2
    resources = tuple(range(pair_count))
    targets = tuple(range(pair_count, 2 * pair_count))
    intermediate = 2 * pair_count if propositions % 2 else None
    # A logical sample defines one stable ordering of all possible conflict edges.
    # Lower densities are therefore prefixes, and hence subsets, of higher densities.
    case_seed = derive_seed(master_seed, propositions, sample, "conflict-order")
    presentation_seed = derive_seed(
        case_seed, source_order, target_order, rule_order, order_sample
    )
    selected_conflicts = select_conflicts(
        pair_count, conflicts, random.Random(case_seed)
    )

    rules = canonical_rules(pair_count, targets, intermediate)
    rules.extend(conflict_rules(selected_conflicts, targets))
    source_presentation, target_presentation, rule_presentation = presentation_orders(
        source_order_mode=source_order,
        target_order_mode=target_order,
        rule_order_mode=rule_order,
        resources=resources,
        targets=targets,
        rules=rules,
        presentation_seed=presentation_seed,
    )

    logical_payload = {
        "schemaVersion": SCHEMA_VERSION,
        "propositions": propositions,
        "resources": resources,
        "targets": targets,
        "intermediate": intermediate,
        "canonicalRules": [
            (rule.premise, rule.conclusion)
            for rule in rules
            if rule.kind == "canonical"
        ],
        "conflicts": [
            (conflict.resource, conflict.target) for conflict in selected_conflicts
        ],
    }
    logical_id = _digest(logical_payload)
    case_id = _digest(
        {
            "logicalId": logical_id,
            "sourceOrderMode": source_order,
            "targetOrderMode": target_order,
            "ruleOrderMode": rule_order,
            "orderSample": order_sample,
            "sourceOrder": source_presentation,
            "targetOrder": target_presentation,
            "ruleOrder": rule_presentation,
            "strategy": strategy,
        }
    )

    case = BenchmarkCase(
        master_seed=master_seed,
        case_seed=case_seed,
        presentation_seed=presentation_seed,
        propositions=propositions,
        requested_conflicts=conflicts,
        requested_density=requested_density,
        sample=sample,
        order_sample=order_sample,
        variant=variant,
        source_order_mode=source_order,
        target_order_mode=target_order,
        rule_order_mode=rule_order,
        strategy=strategy,
        resources=resources,
        targets=targets,
        intermediate=intermediate,
        conflicts=selected_conflicts,
        source_order=source_presentation,
        target_order=target_presentation,
        rules=tuple(rules),
        rule_order=rule_presentation,
        logical_id=logical_id,
        case_id=case_id,
    )
    validate_case(case)
    return case


def validate_case(case: BenchmarkCase) -> None:
    names = case.proposition_names
    used: set[int] = set(case.resources) | set(case.targets)
    if case.intermediate is not None:
        used.add(case.intermediate)
    for rule in case.rules:
        used.add(rule.premise)
        used.add(rule.conclusion)

    if used != set(range(case.propositions)):
        raise AssertionError("not every declared proposition is used")
    if len(case.conflicts) != case.requested_conflicts:
        raise AssertionError("emitted conflict count differs from requested count")
    if case.requested_density is not None and case.requested_conflicts != conflicts_for_density(
        case.propositions, case.requested_density
    ):
        raise AssertionError("emitted conflict count differs from requested density")
    if len(set(case.conflicts)) != len(case.conflicts):
        raise AssertionError("duplicate conflicts were emitted")
    for conflict in case.conflicts:
        if not 0 <= conflict.target < conflict.resource < len(case.resources):
            raise AssertionError("conflict violates the strict triangular invariant")
    if len(case.source_order) != len(case.resources) or set(case.source_order) != set(
        case.resources
    ):
        raise AssertionError("source presentation is not a permutation")
    if len(case.target_order) != len(case.targets) or set(case.target_order) != set(
        range(len(case.targets))
    ):
        raise AssertionError("target presentation is not a permutation")
    if len(case.rule_order) != len(case.rules) or set(case.rule_order) != set(
        range(len(case.rules))
    ):
        raise AssertionError("rule presentation is not a permutation")
    if len(names) != case.propositions:
        raise AssertionError("proposition naming changed the proposition count")


def case_metadata(case: BenchmarkCase) -> dict[str, object]:
    return {
        "schemaVersion": SCHEMA_VERSION,
        "generatorVersion": GENERATOR_VERSION,
        "rngAlgorithm": RNG_ALGORITHM,
        "family": "split",
        "logicalId": case.logical_id,
        "caseId": case.case_id,
        "masterSeed": case.master_seed,
        "caseSeed": case.case_seed,
        "presentationSeed": case.presentation_seed,
        "sample": case.sample,
        "orderSample": case.order_sample,
        "variant": case.variant,
        "sourceOrderMode": case.source_order_mode,
        "targetOrderMode": case.target_order_mode,
        "ruleOrderMode": case.rule_order_mode,
        "strategy": case.strategy,
        "propositions": case.propositions,
        "resourceTargetPairs": len(case.resources),
        "conflicts": case.requested_conflicts,
        "maximumConflicts": maximum_conflicts(case.propositions),
        "requestedConflictDensity": case.requested_density,
        "conflictDensity": realized_density(
            case.propositions, case.requested_conflicts
        ),
        "propositionNames": list(case.proposition_names),
        "resources": [f"P{i}" for i in case.resources],
        "targets": [f"P{i}" for i in case.targets],
        "intermediate": (
            None if case.intermediate is None else f"P{case.intermediate}"
        ),
        "canonicalRules": [
            {
                "name": rule.name,
                "premise": f"P{rule.premise}",
                "conclusion": f"P{rule.conclusion}",
                "targetSlot": rule.target_slot,
            }
            for rule in case.rules
            if rule.kind == "canonical"
        ],
        "conflictRules": [
            {
                "name": rule.name,
                "premise": f"P{rule.premise}",
                "conclusion": f"P{rule.conclusion}",
                "targetSlot": rule.target_slot,
                "stealsCanonicalResourceFromTargetSlot": rule.premise,
            }
            for rule in case.rules
            if rule.kind == "conflict"
        ],
        "presentation": {
            "sourceOrderMode": case.source_order_mode,
            "targetOrderMode": case.target_order_mode,
            "ruleOrderMode": case.rule_order_mode,
            "sourceOrder": [f"P{i}" for i in case.source_order],
            "targetOrder": [f"P{case.targets[i]}" for i in case.target_order],
            "ruleOrder": [case.rules[i].name for i in case.rule_order],
        },
        "invariants": {
            "provableByConstruction": True,
            "uniqueCompleteResourceAssignment": True,
            "conflictGraph": "strict triangular: conflict resource slot > target slot",
        },
    }


def _right_associated_sep(names: Sequence[str]) -> str:
    if not names:
        raise AssertionError("separating conjunction needs at least one term")
    result = names[-1]
    for name in reversed(names[:-1]):
        result = f"{name} ∗ ({result})"
    return result


def _proposition_binders(names: Sequence[str], width: int = 8) -> Iterable[str]:
    for start in range(0, len(names), width):
        yield f"    ({' '.join(names[start:start + width])} : PROP)"


def render_lean(case: BenchmarkCase, *, trace: bool = False) -> str:
    metadata = case_metadata(case)
    sources = [f"P{i}" for i in case.source_order]
    targets = [f"P{case.targets[i]}" for i in case.target_order]
    lines = [
        "module",
        "",
        "public import Iris.BI",
        "public import Iris.ProofMode",
        "",
        "@[expose] public section",
        "",
        "namespace IAesopTest.Benchmark.Generated",
        "open Iris Iris.BI",
        "",
        "/-!",
        "This file is generated by `benchmarks/generate.py`.",
        f"Logical id: {case.logical_id}",
        f"Case id: {case.case_id}",
        f"Configuration: seed={case.master_seed}, propositions={case.propositions}, "
        f"conflicts={case.requested_conflicts}, sample={case.sample}, "
        f"source-order={case.source_order_mode}, target-order={case.target_order_mode}, "
        f"rule-order={case.rule_order_mode}, order-sample={case.order_sample}, "
        f"strategy={case.strategy}",
        "-/",
        "",
        "set_option linter.unusedVariables false in",
    ]
    if trace:
        lines.append("set_option trace.iaesop.search.expand true in")
    lines.extend([
        "example [BI PROP]",
    ])
    lines.extend(_proposition_binders(case.proposition_names))
    for index in case.rule_order:
        rule = case.rules[index]
        lines.append(
            f"    ({rule.name} : P{rule.premise} ⊢ P{rule.conclusion})"
        )
    lines.extend(
        [
            f"    : {_right_associated_sep(sources)} ⊢ {_right_associated_sep(targets)} := by",
            f"  iaesop {case.strategy}",
            "",
            "end IAesopTest.Benchmark.Generated",
            "",
            f"/- benchmark-metadata: {json.dumps(metadata, sort_keys=True, separators=(',', ':'))} -/",
            "",
        ]
    )
    return "\n".join(lines)


def write_text(path: str, contents: str) -> None:
    if path == "-":
        sys.stdout.write(contents)
        return
    output = Path(path)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(contents, encoding="utf-8")


def build_argument_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Generate one deterministic synthetic iaesop benchmark."
    )
    parser.add_argument("--seed", default="0", help="64-bit integer or 'auto'")
    parser.add_argument("--propositions", type=int, default=10)
    ambiguity = parser.add_mutually_exclusive_group()
    ambiguity.add_argument("--conflicts", type=int)
    ambiguity.add_argument(
        "--density",
        help="conflict density from 0 to 1, or a percentage such as 50%%",
    )
    parser.add_argument("--sample", type=int, default=0)
    parser.add_argument("--order-sample", type=int, default=0)
    parser.add_argument(
        "--variant",
        choices=VARIANTS,
        help="compatibility preset; prefer the three independent order options",
    )
    parser.add_argument("--source-order", choices=SOURCE_ORDERS)
    parser.add_argument("--target-order", choices=TARGET_ORDERS)
    parser.add_argument("--rule-order", choices=RULE_ORDERS)
    parser.add_argument("--strategy", choices=STRATEGIES, default="bestFirst")
    parser.add_argument(
        "--output", default="-", help="Lean output path, or '-' for stdout"
    )
    parser.add_argument(
        "--metadata-output", help="optional JSON sidecar output path"
    )
    parser.add_argument(
        "--trace", action="store_true", help="enable iaesop search expansion traces"
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    parser = build_argument_parser()
    args = parser.parse_args(argv)
    try:
        master_seed = parse_seed(args.seed)
        density = None if args.density is None else parse_density(args.density)
        case = build_case(
            master_seed=master_seed,
            propositions=args.propositions,
            conflicts=args.conflicts,
            density=density,
            sample=args.sample,
            order_sample=args.order_sample,
            source_order=args.source_order,
            target_order=args.target_order,
            rule_order=args.rule_order,
            variant=args.variant,
            strategy=args.strategy,
        )
    except ConfigurationError as exc:
        parser.error(str(exc))

    write_text(args.output, render_lean(case, trace=args.trace))
    if args.metadata_output:
        write_text(
            args.metadata_output,
            json.dumps(case_metadata(case), indent=2, sort_keys=True) + "\n",
        )
    print(
        f"generated case={case.case_id} logical={case.logical_id} seed={master_seed}",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
