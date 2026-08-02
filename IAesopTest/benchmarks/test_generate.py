#!/usr/bin/env python3
"""Structural tests for the synthetic iaesop benchmark generator."""

from __future__ import annotations

import itertools
import unittest

from generate import (
    ConfigurationError,
    build_case,
    case_metadata,
    conflicts_for_density,
    maximum_conflicts,
    render_lean,
)


def complete_assignment_count(case: object) -> int:
    pair_count = len(case.resources)
    accepted = [{target} for target in range(pair_count)]
    for conflict in case.conflicts:
        accepted[conflict.target].add(conflict.resource)
    return sum(
        all(permutation[target] in accepted[target] for target in range(pair_count))
        for permutation in itertools.permutations(range(pair_count))
    )


class GeneratorTests(unittest.TestCase):
    def test_generation_is_deterministic(self) -> None:
        first = build_case(
            master_seed=42,
            propositions=10,
            conflicts=6,
            sample=3,
            variant="random",
            strategy="bestFirst",
        )
        second = build_case(
            master_seed=42,
            propositions=10,
            conflicts=6,
            sample=3,
            variant="random",
            strategy="bestFirst",
        )
        self.assertEqual(first, second)
        self.assertEqual(render_lean(first), render_lean(second))

    def test_independent_orders_preserve_the_logical_instance(self) -> None:
        cases = [
            build_case(
                master_seed=7,
                propositions=9,
                conflicts=5,
                sample=2,
                source_order=source_order,
                target_order=target_order,
                rule_order=rule_order,
                strategy="bestFirst",
            )
            for source_order, target_order, rule_order in (
                ("canonical", "canonical", "canonical-first"),
                ("reversed", "canonical", "canonical-first"),
                ("canonical", "constrained-first", "canonical-first"),
                ("canonical", "canonical", "conflict-first"),
                ("random", "random", "random"),
            )
        ]
        self.assertEqual(1, len({case.logical_id for case in cases}))
        self.assertEqual(5, len({case.case_id for case in cases}))
        baseline, source_changed, target_changed, rule_changed, _ = cases
        self.assertNotEqual(baseline.source_order, source_changed.source_order)
        self.assertEqual(baseline.target_order, source_changed.target_order)
        self.assertEqual(baseline.rule_order, source_changed.rule_order)
        self.assertEqual(baseline.source_order, target_changed.source_order)
        self.assertNotEqual(baseline.target_order, target_changed.target_order)
        self.assertEqual(baseline.rule_order, target_changed.rule_order)
        self.assertEqual(baseline.source_order, rule_changed.source_order)
        self.assertEqual(baseline.target_order, rule_changed.target_order)
        self.assertNotEqual(baseline.rule_order, rule_changed.rule_order)

    def test_density_is_converted_and_reported(self) -> None:
        case = build_case(
            master_seed=19,
            propositions=10,
            density=0.25,
            source_order="canonical",
            target_order="canonical",
            rule_order="canonical-first",
        )
        metadata = case_metadata(case)
        self.assertEqual(3, conflicts_for_density(10, 0.25))
        self.assertEqual(3, case.requested_conflicts)
        self.assertEqual(0.25, metadata["requestedConflictDensity"])
        self.assertAlmostEqual(0.3, metadata["conflictDensity"])

    def test_density_levels_add_conflicts_monotonically(self) -> None:
        cases = [
            build_case(
                master_seed=29,
                propositions=20,
                density=density,
            )
            for density in (0.25, 0.5, 0.75, 1.0)
        ]
        for smaller, larger in zip(cases, cases[1:]):
            self.assertTrue(set(smaller.conflicts) < set(larger.conflicts))
            self.assertEqual(smaller.case_seed, larger.case_seed)

    def test_random_order_samples_share_logic_but_change_presentation(self) -> None:
        cases = [
            build_case(
                master_seed=23,
                propositions=12,
                density=0.5,
                order_sample=order_sample,
                source_order="random",
                target_order="random",
                rule_order="random",
            )
            for order_sample in range(3)
        ]
        self.assertEqual(1, len({case.logical_id for case in cases}))
        self.assertEqual(3, len({case.case_id for case in cases}))

    def test_maximal_conflicts_have_one_complete_assignment(self) -> None:
        for propositions in (4, 6, 8, 10):
            case = build_case(
                master_seed=20260802,
                propositions=propositions,
                conflicts=maximum_conflicts(propositions),
                variant="adversarial",
                strategy="bestFirst",
            )
            self.assertEqual(1, complete_assignment_count(case))
            self.assertTrue(
                all(
                    conflict.resource > conflict.target
                    for conflict in case.conflicts
                )
            )

    def test_odd_proposition_is_used_as_canonical_intermediate(self) -> None:
        case = build_case(
            master_seed=11,
            propositions=5,
            conflicts=1,
            variant="canonical",
            strategy="bestFirst",
        )
        metadata = case_metadata(case)
        self.assertEqual("P4", metadata["intermediate"])
        self.assertIn("P4", render_lean(case))
        self.assertEqual(5, len(metadata["propositionNames"]))

    def test_invalid_conflict_request_is_rejected(self) -> None:
        with self.assertRaisesRegex(ConfigurationError, "at most 3"):
            build_case(
                master_seed=0,
                propositions=6,
                conflicts=4,
                variant="canonical",
                strategy="bestFirst",
            )

    def test_conflicts_and_density_are_mutually_exclusive(self) -> None:
        with self.assertRaisesRegex(ConfigurationError, "either conflicts or density"):
            build_case(
                master_seed=0,
                propositions=6,
                conflicts=1,
                density=0.5,
            )


if __name__ == "__main__":
    unittest.main()
