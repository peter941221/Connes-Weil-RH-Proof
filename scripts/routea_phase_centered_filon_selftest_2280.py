"""2280 focused controls."""
import json
import sys
import unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
import routea_phase_centered_filon_tail_screen_2280 as screen

class PhaseCenteredFilonTests(unittest.TestCase):
    def test_current_owner_and_kernel(self):
        _, families, _, _ = screen.load_owner()
        support = 2 * max(width * width for width, _ in families)
        self.assertEqual(len(screen.rig.prime_powers_up_to(__import__("math").exp(support))), 41136)

    def test_polynomial_moment_controls(self):
        for degree in range(6):
            moments = screen.polynomial_moments(0.0, degree)
            expected = 2.0 / (degree + 1) if degree % 2 == 0 else 0.0
            self.assertAlmostEqual(moments[degree].real, expected, places=13)
            self.assertAlmostEqual(moments[degree].imag, 0.0, places=13)

    def test_nonclaim_and_artifact(self):
        artifact = json.loads((screen.ROOT / "results/2280_phase_centered_filon_tail_screen.json").read_text())
        self.assertFalse(artifact["certificate"])
        self.assertFalse(artifact["hgap_closed"])
        self.assertIn("finite xi range is not the infinite tail", artifact["nonclaims"])

if __name__ == "__main__":
    unittest.main()
