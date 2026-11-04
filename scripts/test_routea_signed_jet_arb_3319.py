"""Regression checks for the 3310-directed Arb interval evaluator."""

import unittest
from fractions import Fraction
from pathlib import Path
import subprocess
import sys
import tempfile

from flint import arb, ctx

import routea_signed_jet_rect_arb_probe_3311 as probe


class ArbIntervalRegressionTest(unittest.TestCase):
    def setUp(self):
        ctx.prec = 192

    def test_overlapping_endpoint_balls_enclose_all_products(self):
        left = probe.AInterval(arb("1 +/- 0.5"), arb("2 +/- 0.5"))
        right = probe.AInterval(arb("1.1 +/- 0.5"), arb("2.1 +/- 0.5"))
        product = left.mul(right)
        candidates = [left.lo * right.lo, left.lo * right.hi,
                      left.hi * right.lo, left.hi * right.hi]
        expected_lower = min(Fraction(str(value.lower().fmpq())) for value in candidates)
        expected_upper = max(Fraction(str(value.upper().fmpq())) for value in candidates)
        actual_lower = Fraction(str(product.lo.lower().fmpq()))
        actual_upper = Fraction(str(product.hi.upper().fmpq()))
        self.assertLessEqual(actual_lower, expected_lower)
        self.assertGreaterEqual(actual_upper, expected_upper)

    def test_weight_uses_sixty_factors(self):
        center = Fraction(-6)
        argument = -center / 120
        base = probe.taylor_interval(argument)
        weight = probe.cell_weight_interval(center)
        self.assertTrue(weight.lo > base.hi)
        exponential = arb(3).exp()
        self.assertLessEqual(Fraction(str(weight.lo.lower().fmpq())),
                             Fraction(str(exponential.lower().fmpq())))
        self.assertGreaterEqual(Fraction(str(weight.hi.upper().fmpq())),
                                Fraction(str(exponential.upper().fmpq())))

    def test_manifest_replay_rejects_changed_entry(self):
        root = Path(__file__).resolve().parents[1]
        manifest = root / "ConnesWeilRH/Dev/C1RouteARationalSignedJetBlockManifest3312.lean"
        original = manifest.read_text(encoding="utf-8")
        changed = original.replace(
            "27813974097948817242298065574442126536461551723492123/",
            "27813974097948817242298065574442126536461551723492124/",
            1,
        )
        self.assertNotEqual(original, changed)
        with tempfile.TemporaryDirectory() as directory:
            altered = Path(directory) / "manifest.lean"
            altered.write_text(changed, encoding="utf-8")
            result = subprocess.run(
                [sys.executable, str(root / "scripts/verify_routea_signed_jet_manifest_3313.py"),
                 "--manifest", str(altered)],
                capture_output=True, text=True, encoding="utf-8", check=False,
            )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("block 0: Lean manifest value mismatch", result.stdout)


if __name__ == "__main__":
    unittest.main()
