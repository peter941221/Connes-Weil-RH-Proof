"""2337: sign, analyticity, exact-lifting, and endpoint-error controls."""
from fractions import Fraction
import unittest

from flint import acb, arb, ctx

from routea_marked_sign_arb_certificate_2337 import (
    add_complex_error,
    get_edge_charge,
    get_integrand,
    lift_float,
    lift_fraction,
    serialize_real,
)


class MarkedSignCertificateTests(unittest.TestCase):
    def setUp(self):
        ctx.prec = 256

    def test_lift_uses_exact_binary64_not_short_decimal(self):
        value = lift_float(0.1)
        self.assertTrue(value.is_exact())
        self.assertEqual(value.fmpq(), lift_fraction(Fraction(0.1)).fmpq())
        self.assertFalse(value.contains(arb("1/10")))

    def test_poles_are_rejected_for_analytic_callback(self):
        callback = get_integrand(arb(2), acb(1), arb(0))
        self.assertFalse(callback(acb(1), True).is_finite())
        self.assertFalse(callback(acb(-1), True).is_finite())

    def test_domain_containing_a_pole_is_rejected(self):
        callback = get_integrand(arb(2), acb(1), arb(0))
        self.assertFalse(callback(acb(arb(1, "1/100")), True).is_finite())

    def test_zero_argument_matches_exp_minus_thirty(self):
        callback = get_integrand(arb(2), acb(1), arb(3))
        self.assertTrue(callback(acb(0), True).real.overlaps(arb(-30).exp()))
        self.assertTrue(callback(acb(0), True).imag.is_zero())

    def test_inflated_error_covers_both_complex_coordinates(self):
        value = add_complex_error(acb(1, -1), arb("1/10"))
        self.assertTrue(value.contains(acb(arb("11/10"), arb("-9/10"))))
        self.assertTrue(value.contains(acb(arb("9/10"), arb("-11/10"))))

    def test_large_error_must_refuse_a_negative_sign(self):
        value = add_complex_error(acb(-1), arb(2))
        self.assertFalse(value.real < arb("-99/100"))

    def test_rectangular_serialization_rounds_outward(self):
        value = arb("1/3")
        record = serialize_real(value)
        lower = Fraction(record["lower_exact"])
        upper = Fraction(record["upper_exact"])
        self.assertLess(lower, Fraction(1, 3))
        self.assertGreater(upper, Fraction(1, 3))

    def test_endpoint_charge_stays_positive_below_binary64_range(self):
        charge = get_edge_charge(arb(2), acb(1))
        self.assertTrue(charge > 0)
        self.assertTrue(charge < arb("1e-400"))
        self.assertGreater(Fraction(serialize_real(charge)["upper_exact"]), 0)

    def test_invalid_endpoint_delta_is_rejected(self):
        for delta in (0, 1, -Fraction(1, 64), Fraction(65, 64)):
            with self.assertRaises(ValueError):
                get_edge_charge(arb(2), acb(1), delta)

    def test_companion_product_is_not_the_modulus_square(self):
        first, companion = acb(1), acb(-1)
        paired = companion.conjugate() * first
        self.assertTrue(paired.real < arb("-99/100"))
        self.assertFalse((first.conjugate() * first).real < 0)


if __name__ == "__main__":
    unittest.main()
