"""Regression tests for experiment 174's arm-specific semantic gate."""

from __future__ import annotations

import importlib.util
import unittest
from pathlib import Path

SCRIPT = Path(__file__).parents[1] / "analyze-post-d-e5-r3.py"
SPEC = importlib.util.spec_from_file_location("analyze_post_d_e5_r3", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
ANALYSIS = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(ANALYSIS)


class ArmSpecificSemanticsTests(unittest.TestCase):
    def test_accepts_each_routes_exact_observation_shape(self) -> None:
        row = {
            "control_observed_count": 2,
            "treatment_observed_count": 1,
            "control_firing_visible": 2,
            "treatment_firing_visible": 2,
        }
        self.assertTrue(ANALYSIS.arm_specific_semantics(2, row))

    def test_rejects_equal_observation_counts_when_r3_shape_is_wrong(self) -> None:
        row = {
            "control_observed_count": 2,
            "treatment_observed_count": 2,
            "control_firing_visible": 2,
            "treatment_firing_visible": 2,
        }
        self.assertFalse(ANALYSIS.arm_specific_semantics(2, row))

    def test_rejects_visible_firing_disagreement(self) -> None:
        row = {
            "control_observed_count": 2,
            "treatment_observed_count": 1,
            "control_firing_visible": 2,
            "treatment_firing_visible": 1,
        }
        self.assertFalse(ANALYSIS.arm_specific_semantics(2, row))


if __name__ == "__main__":
    unittest.main()
