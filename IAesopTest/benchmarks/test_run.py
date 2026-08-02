#!/usr/bin/env python3
"""Configuration tests for the synthetic iaesop benchmark runner."""

from __future__ import annotations

import unittest

import run as benchmark_run
from generate import ConfigurationError


class RunnerConfigurationTests(unittest.TestCase):
    def parse(self, *arguments: str):
        return benchmark_run.build_argument_parser().parse_args(list(arguments))

    def test_density_grid_is_kept_separate_from_absolute_conflicts(self) -> None:
        args = self.parse(
            "--propositions",
            "10,20",
            "--densities",
            "0,0.5,1",
        )
        benchmark_run.validate_arguments(args)
        configurations = benchmark_run.build_configurations(args)
        self.assertEqual(6, len(configurations))
        self.assertTrue(all(config.conflicts is None for config in configurations))
        self.assertEqual({0.0, 0.5, 1.0}, {config.density for config in configurations})

    def test_order_dimensions_form_an_explicit_cross_product(self) -> None:
        args = self.parse(
            "--source-orders",
            "canonical",
            "reversed",
            "--target-orders",
            "canonical",
            "constrained-first",
            "--rule-orders",
            "canonical-first",
            "conflict-first",
        )
        benchmark_run.validate_arguments(args)
        configurations = benchmark_run.build_configurations(args)
        self.assertEqual(8, len(configurations))
        self.assertTrue(all(config.variant is None for config in configurations))

    def test_multiple_order_samples_require_randomness(self) -> None:
        args = self.parse("--order-samples", "2")
        with self.assertRaisesRegex(ConfigurationError, "require at least one random"):
            benchmark_run.validate_arguments(args)

        random_args = self.parse(
            "--order-samples",
            "3",
            "--source-orders",
            "random",
        )
        benchmark_run.validate_arguments(random_args)
        self.assertEqual(3, len(benchmark_run.build_configurations(random_args)))


if __name__ == "__main__":
    unittest.main()

