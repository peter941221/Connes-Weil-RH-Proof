"""2277 regression tests for cancellation-preserving owner screen."""
import json
import unittest
from pathlib import Path

import numpy as np
import routea_corrected_cancellation_screen_2277 as screen


class CancellationScreenTests(unittest.TestCase):
    def test_physical_radius_is_squared(self):
        _, families, _, _ = screen.load_owner()
        self.assertTrue(all(width * width > width for width, _ in families if width > 1.0))

    def test_fields_zero_outside_squared_support(self):
        _, families, base, corr = screen.load_owner()
        radius = max(width * width for width, _ in families)
        values, second, third = screen.fields(np.array([radius + 1.0]), families, base)
        self.assertEqual(values[0], 0j)
        self.assertEqual(second[0], 0j)
        self.assertEqual(third[0], 0j)

    def test_grid_refinement_is_stable_in_committed_artifact(self):
        artifact = json.loads((screen.ROOT / "results/2277_corrected_cancellation_screen.json").read_text())
        self.assertLess(artifact["refinement"]["relative_B_change"], 1e-9)
        self.assertGreater(artifact["refinement"]["fine_B"], 0.0)

    def test_cancellation_beats_rejected_familywise_bound(self):
        artifact = json.loads((screen.ROOT / "results/2277_corrected_cancellation_screen.json").read_text())
        observed = artifact["refinement"]["fine_B"]
        rejected = artifact["rejected_familywise"]["base_D2"][1] * artifact["rejected_familywise"]["corr_D0"][1]
        self.assertLess(observed, rejected)

    def test_tail_is_not_claimed_closed(self):
        artifact = json.loads((screen.ROOT / "results/2277_corrected_cancellation_screen.json").read_text())
        self.assertFalse(artifact["certificate"])
        self.assertFalse(artifact["hgap_closed"])
        self.assertIn("not analytic enclosures", "sampled trapezoids are not analytic enclosures")

    def test_third_derivative_has_bump_term(self):
        source = (screen.ROOT / "scripts/routea_corrected_cancellation_screen_2277.py").read_text()
        self.assertIn("third_log + 3.0 * first_log * second_log + first_log ** 3", source)


if __name__ == "__main__":
    unittest.main()
