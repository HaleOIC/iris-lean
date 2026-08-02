#!/usr/bin/env python3
"""Run deterministic synthetic iaesop benchmarks and emit JSON Lines results."""

from __future__ import annotations

import argparse
import json
import platform
import subprocess
import sys
import tempfile
import time
from collections import defaultdict
from dataclasses import dataclass
from itertools import product
from pathlib import Path
from typing import Sequence

from generate import (
    ConfigurationError,
    RULE_ORDERS,
    SOURCE_ORDERS,
    STRATEGIES,
    TARGET_ORDERS,
    VARIANT_PRESETS,
    VARIANTS,
    build_case,
    case_metadata,
    conflicts_for_density,
    parse_density,
    parse_seed,
    render_lean,
    validate_configuration,
)


RESULT_SCHEMA_VERSION = 2


@dataclass(frozen=True)
class RunConfiguration:
    propositions: int
    conflicts: int | None
    density: float | None
    sample: int
    order_sample: int
    variant: str | None
    source_order: str | None
    target_order: str | None
    rule_order: str | None
    strategy: str


def parse_integer_list(value: str) -> list[int]:
    result: list[int] = []
    for item in value.split(","):
        item = item.strip()
        if not item:
            continue
        try:
            result.append(int(item, 0))
        except ValueError as exc:
            raise argparse.ArgumentTypeError(
                f"expected a comma-separated integer list, got {value!r}"
            ) from exc
    if not result:
        raise argparse.ArgumentTypeError("integer list cannot be empty")
    return result


def parse_density_list(value: str) -> list[float]:
    result: list[float] = []
    for item in value.split(","):
        item = item.strip()
        if not item:
            continue
        try:
            result.append(parse_density(item))
        except ConfigurationError as exc:
            raise argparse.ArgumentTypeError(str(exc)) from exc
    if not result:
        raise argparse.ArgumentTypeError("density list cannot be empty")
    return result


def command_output(command: Sequence[str], cwd: Path) -> str:
    try:
        completed = subprocess.run(
            command,
            cwd=cwd,
            check=True,
            capture_output=True,
            text=True,
            timeout=30,
        )
    except (OSError, subprocess.SubprocessError) as exc:
        return f"unavailable: {exc}"
    return (completed.stdout or completed.stderr).strip()


def classify_failure(output: str) -> str:
    lowered = output.lower()
    if "internal error" in lowered:
        return "internal_error"
    if "replay" in lowered and "error:" in lowered:
        return "replay_failure"
    if "settlement" in lowered and "error:" in lowered:
        return "settlement_failure"
    if "unknown module" in lowered or "search path" in lowered:
        return "environment_error"
    if "unsolved goals" in lowered or "tactic" in lowered:
        return "tactic_failure"
    return "lean_error"


def run_lean(
    *, lean_file: Path, lake_dir: Path, timeout: float
) -> tuple[str, float, int | None, str]:
    command = ["lake", "env", "lean", str(lean_file)]
    started = time.perf_counter()
    try:
        completed = subprocess.run(
            command,
            cwd=lake_dir,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired as exc:
        elapsed = time.perf_counter() - started
        partial = "".join(
            part.decode("utf-8", errors="replace") if isinstance(part, bytes) else (part or "")
            for part in (exc.stdout, exc.stderr)
        )
        return "timeout", elapsed, None, partial
    except OSError as exc:
        elapsed = time.perf_counter() - started
        return "environment_error", elapsed, None, str(exc)

    elapsed = time.perf_counter() - started
    output = (completed.stdout or "") + (completed.stderr or "")
    status = "success" if completed.returncode == 0 else classify_failure(output)
    return status, elapsed, completed.returncode, output


def environment_metadata(lake_dir: Path) -> dict[str, object]:
    return {
        "gitCommit": command_output(["git", "rev-parse", "HEAD"], lake_dir),
        "leanVersion": command_output(["lake", "env", "lean", "--version"], lake_dir),
        "platform": platform.platform(),
        "machine": platform.machine(),
        "processor": platform.processor(),
        "pythonVersion": platform.python_version(),
    }


def diagnostic_tail(output: str, maximum_lines: int = 40) -> str:
    return "\n".join(output.splitlines()[-maximum_lines:])


def build_argument_parser() -> argparse.ArgumentParser:
    script_dir = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(
        description="Generate and run a grid of synthetic iaesop benchmarks."
    )
    parser.add_argument("--seed", default="0", help="64-bit integer or 'auto'")
    parser.add_argument(
        "--propositions",
        type=parse_integer_list,
        default=[10],
        help="one value or a comma-separated list",
    )
    ambiguity = parser.add_mutually_exclusive_group()
    ambiguity.add_argument(
        "--conflicts",
        type=parse_integer_list,
        help="one value or a comma-separated list",
    )
    ambiguity.add_argument(
        "--densities",
        type=parse_density_list,
        help="comma-separated densities, for example 0,0.25,0.5,0.75,1",
    )
    parser.add_argument("--samples", type=int, default=1)
    parser.add_argument("--order-samples", type=int, default=1)
    parser.add_argument(
        "--variants",
        nargs="+",
        choices=VARIANTS,
        help="compatibility presets; cannot be combined with independent order controls",
    )
    parser.add_argument("--source-orders", nargs="+", choices=SOURCE_ORDERS)
    parser.add_argument("--target-orders", nargs="+", choices=TARGET_ORDERS)
    parser.add_argument("--rule-orders", nargs="+", choices=RULE_ORDERS)
    parser.add_argument(
        "--strategies", nargs="+", choices=STRATEGIES, default=["bestFirst"]
    )
    parser.add_argument("--repetitions", type=int, default=1)
    parser.add_argument("--timeout", type=float, default=30.0)
    parser.add_argument(
        "--lake-dir",
        type=Path,
        default=script_dir.parent,
        help="IAesopTest Lake package directory",
    )
    parser.add_argument(
        "--results",
        type=Path,
        default=script_dir / "results" / "latest.jsonl",
        help="JSON Lines result path",
    )
    parser.add_argument(
        "--keep-inputs",
        type=Path,
        help="optional directory in which to retain all generated Lean inputs",
    )
    parser.add_argument(
        "--no-warmup", action="store_true", help="skip the unmeasured first run"
    )
    return parser


def selected_order_configurations(
    args: argparse.Namespace,
) -> list[tuple[str | None, str | None, str | None, str | None]]:
    independent = (args.source_orders, args.target_orders, args.rule_orders)
    if args.variants:
        if any(value is not None for value in independent):
            raise ConfigurationError(
                "variants cannot be combined with independent order controls"
            )
        return [(variant, None, None, None) for variant in args.variants]

    source_orders = args.source_orders or ["canonical"]
    target_orders = args.target_orders or ["canonical"]
    rule_orders = args.rule_orders or ["canonical-first"]
    return [
        (None, source_order, target_order, rule_order)
        for source_order, target_order, rule_order in product(
            source_orders, target_orders, rule_orders
        )
    ]


def build_configurations(
    args: argparse.Namespace,
) -> list[RunConfiguration]:
    order_configurations = selected_order_configurations(args)
    ambiguity_configurations: list[tuple[int | None, float | None]]
    if args.densities is not None:
        ambiguity_configurations = [(None, density) for density in args.densities]
    else:
        ambiguity_configurations = [
            (conflicts, None) for conflicts in (args.conflicts or [0])
        ]
    return [
        RunConfiguration(
            propositions=propositions,
            conflicts=conflicts,
            density=density,
            sample=sample,
            order_sample=order_sample,
            variant=variant,
            source_order=source_order,
            target_order=target_order,
            rule_order=rule_order,
            strategy=strategy,
        )
        for propositions in args.propositions
        for conflicts, density in ambiguity_configurations
        for sample in range(args.samples)
        for order_sample in range(args.order_samples)
        for variant, source_order, target_order, rule_order in order_configurations
        for strategy in args.strategies
    ]


def validate_arguments(args: argparse.Namespace) -> None:
    if args.samples < 1:
        raise ConfigurationError("samples must be at least 1")
    if args.order_samples < 1:
        raise ConfigurationError("order samples must be at least 1")
    if args.repetitions < 1:
        raise ConfigurationError("repetitions must be at least 1")
    if args.timeout <= 0:
        raise ConfigurationError("timeout must be positive")
    order_configurations = selected_order_configurations(args)
    if args.order_samples > 1:
        has_random_order = any(
            variant == "random"
            or "random" in (source_order, target_order, rule_order)
            for variant, source_order, target_order, rule_order in order_configurations
        )
        if not has_random_order:
            raise ConfigurationError(
                "order samples above 1 require at least one random order dimension"
            )
    for propositions in args.propositions:
        conflict_counts = (
            [conflicts_for_density(propositions, density) for density in args.densities]
            if args.densities is not None
            else (args.conflicts or [0])
        )
        for conflicts in conflict_counts:
            validate_configuration(propositions, conflicts, 0)
    if not (args.lake_dir / "lakefile.toml").is_file():
        raise ConfigurationError(
            f"lake directory does not contain lakefile.toml: {args.lake_dir}"
        )


def materialize_case(master_seed: int, config: RunConfiguration):
    return build_case(
        master_seed=master_seed,
        propositions=config.propositions,
        conflicts=config.conflicts,
        density=config.density,
        sample=config.sample,
        order_sample=config.order_sample,
        variant=config.variant,
        source_order=config.source_order,
        target_order=config.target_order,
        rule_order=config.rule_order,
        strategy=config.strategy,
    )


def main(argv: Sequence[str] | None = None) -> int:
    parser = build_argument_parser()
    args = parser.parse_args(argv)
    try:
        master_seed = parse_seed(args.seed)
        validate_arguments(args)
    except ConfigurationError as exc:
        parser.error(str(exc))

    lake_dir = args.lake_dir.resolve()
    environment = environment_metadata(lake_dir)
    args.results.parent.mkdir(parents=True, exist_ok=True)
    if args.keep_inputs:
        args.keep_inputs.mkdir(parents=True, exist_ok=True)

    configurations = build_configurations(args)
    total = len(configurations) * args.repetitions
    observations: list[dict[str, object]] = []

    with tempfile.TemporaryDirectory(prefix="iaesop-benchmark-") as temporary:
        temporary_dir = Path(temporary)

        if not args.no_warmup:
            warmup = materialize_case(master_seed, configurations[0])
            warmup_file = temporary_dir / "warmup.lean"
            warmup_file.write_text(render_lean(warmup), encoding="utf-8")
            run_lean(lean_file=warmup_file, lake_dir=lake_dir, timeout=args.timeout)

        completed_count = 0
        for config in configurations:
            case = materialize_case(master_seed, config)
            lean_text = render_lean(case)
            lean_file = temporary_dir / f"case-{case.case_id}.lean"
            lean_file.write_text(lean_text, encoding="utf-8")
            if args.keep_inputs:
                retained = args.keep_inputs / f"case-{case.case_id}.lean"
                retained.write_text(lean_text, encoding="utf-8")

            for repetition in range(args.repetitions):
                status, elapsed, return_code, output = run_lean(
                    lean_file=lean_file, lake_dir=lake_dir, timeout=args.timeout
                )
                completed_count += 1
                metadata = case_metadata(case)
                observation: dict[str, object] = {
                    "resultSchemaVersion": RESULT_SCHEMA_VERSION,
                    **metadata,
                    **environment,
                    "repetition": repetition,
                    "timeoutSeconds": args.timeout,
                    "status": status,
                    "kernelChecked": status == "success",
                    "processWallTimeMs": round(elapsed * 1000, 3),
                    "returnCode": return_code,
                }
                if status != "success":
                    observation["diagnosticTail"] = diagnostic_tail(output)
                observations.append(observation)
                print(
                    f"[{completed_count}/{total}] {status} "
                    f"p={config.propositions} c={case.requested_conflicts} "
                    f"density={float(metadata['conflictDensity']):.3f} "
                    f"sample={config.sample} order-sample={config.order_sample} "
                    f"source={case.source_order_mode} target={case.target_order_mode} "
                    f"rule={case.rule_order_mode} strategy={config.strategy} {elapsed:.3f}s",
                    file=sys.stderr,
                )

    with args.results.open("w", encoding="utf-8") as result_file:
        for observation in observations:
            result_file.write(json.dumps(observation, sort_keys=True) + "\n")

    status_counts: dict[str, int] = defaultdict(int)
    paired: dict[tuple[str, str, int], set[str]] = defaultdict(set)
    for observation in observations:
        status = str(observation["status"])
        status_counts[status] += 1
        paired[
            (
                str(observation["logicalId"]),
                str(observation["strategy"]),
                int(observation["repetition"]),
            )
        ].add(status)
    disagreements = sum(len(statuses) > 1 for statuses in paired.values())
    print(
        f"seed={master_seed} results={args.results} statuses={dict(status_counts)} "
        f"pairedStatusDisagreements={disagreements}",
        file=sys.stderr,
    )
    return 0 if status_counts.get("success", 0) == total else 1


if __name__ == "__main__":
    raise SystemExit(main())
