"""Artifact and majorant-shape controls for 2304 (flat-edge tail probe).

Keeps the committed artifact honest: the two ladders must have their
documented lengths and monotonicity, the rigorous ladder must dominate the
measured one at every compared order, the tail minimum must sit at the
recorded order, and every calibration ratio must stay >= 1 (the IBP bound
must not undercut the measured single-family transform).
"""
import json
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
ART = ROOT / "results" / "2304_hgap_tail_moment_probe.json"
BUDGET = 1.0e7


class TailMomentControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.art = json.loads(ART.read_text(encoding="utf-8"))

    def test_scope_and_verdict(self):
        self.assertEqual(self.art["status"], "TAIL-MOMENT-DEAD")
        self.assertFalse(self.art["certificate"])
        self.assertEqual(self.art["budget"], BUDGET)
        self.assertEqual(self.art["xi0"], 40.0)
        self.assertIn("no boundary terms", self.art["mechanism"])

    def test_ladder_shape(self):
        measured = self.art["sup_ladder_measured"]
        rigorous = self.art["sup_ladder_rigorous"]
        ratios = self.art["rigorous_over_measured"]
        self.assertEqual(len(measured), 21)      # j = 0..20, float64 grid max
        self.assertEqual(len(rigorous), 45)      # j = 0..44, closed-form majorant
        self.assertEqual(len(ratios), len(measured))
        # the rigorous partition majorant dominates the measured ladder
        for value in ratios:
            self.assertGreaterEqual(float(value), 1.0)
        # and the gap is monotone increasing in the order
        vals = [float(v) for v in ratios]
        self.assertTrue(all(b > a for a, b in zip(vals, vals[1:])))

    def test_best_order_is_the_minimum(self):
        rows = self.art["rows"]
        bounds = {r["order"]: r["tail_bound_rigorous_float"] for r in rows}
        best = min(bounds, key=bounds.get)
        self.assertEqual(best, self.art["best_order"])
        self.assertEqual(self.art["best_order"], 28)
        self.assertAlmostEqual(self.art["best_tail_bound_float"],
                               bounds[best], delta=1e-6 * bounds[best])
        self.assertGreater(bounds[best], BUDGET)

    def test_every_order_dead(self):
        rows = self.art["rows"]
        self.assertEqual([r["order"] for r in rows],
                         [3, 4, 6, 8, 10, 12, 14, 16, 20, 24, 28, 32, 36, 40, 44])
        self.assertEqual(len(self.art["orders_dead"]), len(rows))
        for r in rows:
            self.assertGreater(r["tail_bound_rigorous_float"], BUDGET)
            if "tail_bound_measured_float" in r:
                self.assertGreaterEqual(r["tail_bound_rigorous_float"],
                                        r["tail_bound_measured_float"])
        # the measured ladder clears the budget at the recorded high orders
        measured = {r["order"]: r["tail_bound_measured_float"] for r in rows
                    if "tail_bound_measured_float" in r}
        self.assertLess(measured[20], BUDGET)
        self.assertLess(measured[16], 1.0e3)

    def test_inputs_pinned(self):
        ann = self.art["annihilator"]
        self.assertEqual(len(ann["coeffs"]), 5)
        for odd in ann["coeffs"][1::2]:
            self.assertLess(abs(odd), 1e-8)
        self.assertAlmostEqual(ann["l1"], 2497731.388738144,
                               delta=1e-9 * ann["l1"])
        kernel = self.art["kernel"]
        self.assertEqual(kernel["prime_power_count"], 41136)
        self.assertAlmostEqual(kernel["prime_sum"], 2801.5021085164085,
                               delta=1e-12 * kernel["prime_sum"])
        self.assertAlmostEqual(kernel["c_w"], kernel["c_sigma"]
                               + kernel["prime_sum"], delta=1e-9)

    def test_calibration_ratios_cover(self):
        rows = self.art["calibration"]["rows"]
        self.assertEqual([r["xi"] for r in rows], [1.0, 2.0, 4.0])
        for r in rows:
            best = min(float(b["ratio"]) for b in r["bounds"])
            self.assertGreaterEqual(best, 1.0)


if __name__ == "__main__":
    unittest.main()