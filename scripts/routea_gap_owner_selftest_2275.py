"""Exact controls for record 2275; no numerical search or full-grid run."""
from fractions import Fraction
import copy
import json
import unittest

import routea_gap_owner_audit_2275 as audit


class GapAuditTests(unittest.TestCase):
    def test_exact_refinement_counterexample(self):
        self.assertEqual(audit.refinement_counterexample(),
                         (Fraction(0), Fraction(0), Fraction(20000000)))

    def test_counterexample_can_exceed_any_finite_budget(self):
        for budget in (1, 10000000, 10 ** 100):
            coarse, fine, integral = audit.refinement_counterexample(240 * budget)
            self.assertEqual(coarse, fine)
            self.assertGreater(integral, budget)

    def test_common_period_exact(self):
        frequencies = [Fraction.from_float(width) * Fraction.from_float(point)
                       for width, point in ((0.8, 0.1), (2.56, -0.3), (1.76, 0.5))]
        exponent = audit.dyadic_period_exponent(frequencies)
        for frequency in frequencies:
            self.assertEqual((frequency * 2 ** exponent).denominator, 1)

    def test_extreme_binary64_product(self):
        smallest = Fraction.from_float(float.fromhex("0x0.0000000000001p-1022"))
        self.assertEqual(audit.dyadic_period_exponent([smallest * smallest]), 2148)

    def test_non_dyadic_rejected(self):
        with self.assertRaises(ValueError):
            audit.dyadic_period_exponent([Fraction(1, 3)])

    def test_source_control_and_change_detection(self):
        source = (audit.ROOT / audit.INPUTS[1]).read_text()
        self.assertTrue(audit.check_refinement_source(source))
        changed = source.replace("base = np.linalg.solve(a_mat, np.ones(len(nodes), complex))",
                                 "base = frozen_base")
        self.assertFalse(audit.check_refinement_source(changed))

    def test_audit_retains_open_gap(self):
        result = audit.build_audit()
        self.assertFalse(result["hgap_closed"])
        self.assertIsNone(result["owner_capture"])
        self.assertEqual(result["historical_measured_gap"], 6537949.749302972)

    def test_trapezoid_coefficient_exact(self):
        self.assertEqual(Fraction(80) * Fraction(1, 50) ** 2 / 12, Fraction(1, 375))

    def test_committed_owner_capture_and_corruption(self):
        artifact = json.loads((audit.ROOT / "results/2275_gap_owner_audit.json").read_text())
        baseline = json.loads((audit.ROOT / audit.INPUTS[2]).read_text())["diagnostics"]
        captured = artifact["owner_capture"]
        audit.verify_capture(captured, baseline)
        corrupted = copy.deepcopy(captured)
        corrupted["base_hex"][0][0] = "0x0.0p+0"
        with self.assertRaisesRegex(ValueError, "coefficient anchor"):
            audit.verify_capture(corrupted, baseline)

    def test_committed_artifact_input_hashes(self):
        artifact = json.loads((audit.ROOT / "results/2275_gap_owner_audit.json").read_text())
        replay = audit.build_audit(artifact["owner_capture"])
        self.assertEqual(replay, artifact)


if __name__ == "__main__":
    unittest.main()
