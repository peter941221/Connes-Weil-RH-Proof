"""Exact recurrence, invalid-geometry, and independent-precision controls."""
from fractions import Fraction
import unittest

from flint import arb, ctx, fmpq

from analytic_moment_residual_probe_2619 import build_panel, run


class ResidualModelTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.primary = run((8, 32, 48), precision=384)
        cls.control = run((32,), precision=512)

    def test_initial_coefficient_and_first_derivatives(self):
        panel = build_panel(fmpq(3), fmpq(0), fmpq(1, 200), 8)
        self.assertEqual(panel["coefficients"][:3], [1, 3, fmpq(-51, 2)])

    def test_unmodulated_center_has_no_odd_coefficients(self):
        panel = build_panel(fmpq(0), fmpq(0), fmpq(1, 200), 16)
        self.assertTrue(all(value == 0 for value in panel["coefficients"][1::2]))

    def test_only_five_high_order_residual_slots_remain(self):
        panel = build_panel(fmpq(7, 3), fmpq(4, 5), fmpq(1, 200), 32)
        self.assertTrue(all(value == 0 for value in panel["residual"][:32]))
        self.assertEqual(len(panel["residual"]), 37)
        self.assertTrue(any(value != 0 for value in panel["residual"][32:]))

    def test_residual_reconstructs_differential_equation(self):
        beta, center, position = Fraction(7, 3), Fraction(4, 5), Fraction(1, 1000)
        panel = build_panel(fmpq(7, 3), fmpq(4, 5), fmpq(1, 200), 8)
        coefficients = [Fraction(int(value.numerator), int(value.denominator))
                        for value in panel["coefficients"]]
        residual = [Fraction(int(value.numerator), int(value.denominator))
                    for value in panel["residual"]]
        polynomial = sum(value * position ** index for index, value in enumerate(coefficients))
        derivative = sum(index * value * position ** (index - 1)
                         for index, value in enumerate(coefficients) if index)
        denominator = (1 - (center + position) ** 2) ** 2
        numerator = beta * denominator - 60 * (center + position)
        self.assertEqual(sum(value * position ** index for index, value in enumerate(residual)),
                         denominator * derivative - numerator * polynomial)

    def test_singular_panel_is_rejected(self):
        with self.assertRaises(ValueError):
            build_panel(fmpq(1), fmpq(9, 10), fmpq(1, 10), 8)

    def test_zero_degree_is_rejected(self):
        with self.assertRaises(ValueError):
            build_panel(fmpq(1), fmpq(0), fmpq(1, 200), 0)

    def test_nonpositive_width_is_rejected(self):
        for width in (fmpq(0), fmpq(-1, 200)):
            with self.assertRaises(ValueError):
                build_panel(fmpq(1), fmpq(0), width, 8)

    def test_low_order_candidate_fails_unchanged_box(self):
        self.assertFalse(self.primary["rows"][0]["fits_2597_under_stability_and_edge_bounds"])

    def test_degree_32_and_48_fit_unchanged_box(self):
        self.assertTrue(all(row["fits_2597_under_stability_and_edge_bounds"]
                            for row in self.primary["rows"][1:]))

    def test_independent_precision_preserves_enclosure(self):
        ctx.prec = 512
        first, second = self.primary["rows"][1], self.control["rows"][0]
        for component in ("core_integral",):
            first_lo = arb(first[component]["lower_exact"])
            first_hi = arb(first[component]["upper_exact"])
            second_lo = arb(second[component]["lower_exact"])
            second_hi = arb(second[component]["upper_exact"])
            self.assertTrue(first_lo <= second_hi and second_lo <= first_hi)
        self.assertLessEqual(fmpq(second["interior_charge"]["upper_exact"]),
                             fmpq(first["interior_charge"]["upper_exact"]))
        self.assertTrue(second["fits_2597_under_stability_and_edge_bounds"])
        self.assertEqual(first["coefficient_and_residual_sha256"],
                         second["coefficient_and_residual_sha256"])

    def test_numeric_reading_is_not_claimed_as_lean_membership(self):
        self.assertFalse(self.primary["actual_entry_containment_lean_verified"])
        self.assertFalse(self.primary["producer_go"])
        self.assertFalse(self.primary["rh_claim"])


if __name__ == "__main__":
    unittest.main()
