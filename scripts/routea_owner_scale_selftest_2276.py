"""2276 controls: exact ownership, directed arithmetic and method-scoped verdicts."""
from fractions import Fraction
import json
import re
import unittest
from unittest.mock import patch

import mpmath as mp
import routea_owner_scale_price_2276 as price


class ScalePriceTests(unittest.TestCase):
    def setUp(self):
        self.engine = price.DirectedEngine()
        price.ENGINE = self.engine

    def tearDown(self):
        self.engine.close()
        price.ENGINE = None

    def test_fraction_construction_outward(self):
        for rational in (Fraction(1, 3), Fraction(-1, 7), Fraction(10 ** 20 + 1, 10 ** 20)):
            interval = price.Interval.exact(rational)
            self.assertLessEqual(Fraction(interval.lo), rational)
            self.assertGreaterEqual(Fraction(interval.hi), rational)

    def test_binary_operations_outward(self):
        for left, right in ((Fraction(1, 3), Fraction(1, 7)),
                            (Fraction(-7, 3), Fraction(5, 9))):
            left_interval = price.Interval.exact(left)
            right_interval = price.Interval.exact(right)
            for interval, exact in ((left_interval + right_interval, left + right),
                                    (left_interval - right_interval, left - right),
                                    (left_interval * right_interval, left * right),
                                    (left_interval / right_interval, left / right)):
                self.assertLessEqual(Fraction(interval.lo), exact)
                self.assertGreaterEqual(Fraction(interval.hi), exact)

    def test_unary_against_independent_engine(self):
        with mp.workdps(100):
            for argument in (Fraction(-30), Fraction(-185), Fraction(1, 7)):
                interval = price.Interval.exact(argument).unary("mpfr_exp")
                reference = mp.exp(mp.mpf(argument.numerator) / argument.denominator)
                self.assertLessEqual(mp.mpf(interval.lo), reference)
                self.assertGreaterEqual(mp.mpf(interval.hi), reference)
            root = price.Interval.exact(2).unary("mpfr_sqrt")
            self.assertLessEqual(mp.mpf(root.lo), mp.sqrt(2))
            self.assertGreaterEqual(mp.mpf(root.hi), mp.sqrt(2))

    def test_invalid_intervals_rejected(self):
        for pair in ((2.0, 1.0), (0.0, float("inf")), (float("nan"), 1.0)):
            with self.assertRaises(ValueError):
                price.Interval(*pair)

    def test_zero_divisor_rejected(self):
        with self.assertRaises(ValueError):
            price.Interval.exact(1) / price.Interval(-1, 1)

    def test_negative_sqrt_and_power_rejected(self):
        with self.assertRaises(ValueError):
            price.Interval(-2, -1).unary("mpfr_sqrt")
        with self.assertRaises(ValueError):
            price.Interval.exact(1).power(-1)

    def test_only_fourth_corrected_family_survives(self):
        capture = json.loads((price.ROOT / price.INPUTS[0]).read_text())["owner_capture"]
        widths = [price.stored_rational(value[0]) for value in capture["families_hex"]]
        self.assertTrue(all(width < 6 for width in widths))
        self.assertEqual([index for index, width in enumerate(widths) if width ** 2 > 6], [4])

    def test_original_coefficient_anchors_unchanged(self):
        artifact = json.loads((price.ROOT / "results/2276_owner_scale_price.json").read_text())
        self.assertEqual(artifact["coefficient_component_mismatches"], {"base": 0, "corr": 0})
        for pair in artifact["corrected_magnitude_at_six_enclosures"].values():
            self.assertGreater(pair[0], 0)

    def test_derivative_triangle_constant(self):
        self.assertEqual(72 * 30 + 60 * 30 ** 2 + 8 * 30 ** 3, 272160)

    def test_lean_literals_match_stored_operands(self):
        source = (price.ROOT / "ConnesWeilRH/Dev/C1RouteAOwnerScaleAudit.lean").read_text()
        captured = json.loads((price.ROOT / price.INPUTS[0]).read_text())["owner_capture"]
        array = re.search(r"def storedWidth.*?!\[(.*?)\]", source, re.S).group(1)
        widths = [Fraction(value.strip().strip("()").replace(" ", ""))
                  for value in array.split(",")]
        self.assertEqual(widths, [price.stored_rational(pair[0]) for pair in captured["families_hex"]])
        for side, definition in (("base", "storedBaseFour"), ("corr", "storedCorrFour")):
            expression = re.search(r"def " + definition + r".*?:=(.*?)(?=\n\n)", source, re.S).group(1)
            values = [Fraction(value.replace(" ", ""))
                      for value in re.findall(r"-?\d+ / \d+", expression)]
            self.assertEqual(values, [price.stored_rational(value) for value in captured[side + "_hex"][4]])

    def test_source_control_fails_closed(self):
        with patch.object(price, "source_controls", return_value={"changed": False}):
            with self.assertRaisesRegex(ValueError, "source control"):
                price.build_price()

    def test_committed_price_replay_exact(self):
        artifact = json.loads((price.ROOT / "results/2276_owner_scale_price.json").read_text())
        self.assertEqual(price.build_price(), artifact)

    def test_verdict_is_method_scoped(self):
        artifact = json.loads((price.ROOT / "results/2276_owner_scale_price.json").read_text())
        self.assertFalse(artifact["hgap_closed"])
        self.assertEqual(artifact["price_status"], "ABSOLUTE-FAMILY-METHOD-REJECTED")
        self.assertGreater(artifact["method_price_ratios"]["strip"][0], 1)
        self.assertGreater(artifact["method_price_ratios"]["ideal_tail"][0], 1)
        self.assertIn("not lower bounds", artifact["enclosure_scope"])


if __name__ == "__main__":
    unittest.main()
