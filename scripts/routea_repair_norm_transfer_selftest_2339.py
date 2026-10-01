"""2339: edge, phase, geometry, two-sided tail and provenance controls."""
from fractions import Fraction
import tempfile
from pathlib import Path
import unittest

from flint import arb, ctx
import routea_repair_norm_transfer_2339 as transfer


class RepairTransferTests(unittest.TestCase):
    def setUp(self):
        ctx.prec = 320

    def test_derivative_constants_cover_independent_polynomial_recurrence(self):
        polynomial = {0: 1}
        constants = [1, 60, 3900, 272160]
        for order in range(4):
            self.assertLessEqual(sum(abs(value) for value in polynomial.values()), constants[order])
            next_polynomial = {}
            for power, coefficient in polynomial.items():
                terms = [(power + 1, -60 * coefficient),
                         (power + 1, 4 * order * coefficient),
                         (power + 3, -4 * order * coefficient)]
                if power:
                    terms += [(power - 1, power * coefficient),
                              (power + 1, -2 * power * coefficient),
                              (power + 3, power * coefficient)]
                for exponent, value in terms:
                    next_polynomial[exponent] = next_polynomial.get(exponent, 0) + value
            polynomial = {power: value for power, value in next_polynomial.items() if value}

    def test_zero_repair_and_exact_radius_have_zero_charges(self):
        delta, geometry = transfer.moment_charges(arb(2), arb(2), arb(19), arb(30), arb(0), arb("1/2"))
        self.assertTrue(all(value.is_zero() for value in delta + geometry))

    def test_squared_width_rounding_is_not_silently_zeroed(self):
        width = transfer.certificate.lift_float(1.76)
        radius = width * width
        old = transfer.certificate.lift_float(1.76**2)
        self.assertFalse((radius - old).is_zero())
        _, geometry = transfer.moment_charges(radius, old, arb(19), arb(30), arb(0), arb("1/2"))
        self.assertTrue(all(value > 0 for value in geometry))

    def test_phase_terms_are_charged_in_first_and_second_derivatives(self):
        plain, _ = transfer.moment_charges(arb(2), arb(2), arb(0), arb(1), arb(1), arb(0))
        modulated, _ = transfer.moment_charges(arb(2), arb(2), arb(100), arb(1), arb(1), arb(0))
        self.assertTrue(plain[0].overlaps(modulated[0]))
        self.assertTrue(modulated[1] > plain[1])
        self.assertTrue(modulated[2] > plain[2])
        self.assertTrue(modulated[2] > 10000 * plain[0])

    def test_sigma_and_phase_signs_have_identical_upper_charges(self):
        positive = transfer.moment_charges(arb(2), arb(3), arb(19), arb(30), arb(1), arb("1/2"))
        negative = transfer.moment_charges(arb(2), arb(3), arb(-19), arb(30), arb(1), arb("-1/2"))
        self.assertEqual([[transfer.endpoint(value) for value in terms] for terms in positive],
                         [[transfer.endpoint(value) for value in terms] for terms in negative])

    def test_zero_radius_and_nonpositive_step_are_rejected(self):
        with self.assertRaises(ValueError):
            transfer.moment_charges(arb(0), arb(1), arb(0), arb(1), arb(1), arb(0))
        with self.assertRaises(ValueError):
            transfer.first_norm(arb(1), arb(1), arb(0), Fraction(0))

    def test_delta_endpoint_validation_rejects_negative_or_inverted(self):
        for lower, upper in (("-1", "2"), ("3", "2")):
            with self.assertRaises(ValueError):
                transfer.delta_upper({"base_delta_abs": {"lower_exact": lower, "upper_exact": upper}}, "base")

    def test_no_float_underflow_in_tail(self):
        pairs = [[arb("1e-1000"), arb("1e-1000")]] * 4
        numerator = transfer.tail_numerator(pairs)
        self.assertTrue(numerator > 0)
        self.assertNotEqual(transfer.endpoint(numerator)["upper_exact"], "0")

    def test_both_frequency_signs_have_identical_square_envelopes(self):
        pairs = [[arb(2), arb(3)], [arb(4), arb(5)], [arb(1), arb(2)], [arb(3), arb(4)]]
        self.assertEqual(transfer.endpoint(transfer.square_change(pairs, arb(7))),
                         transfer.endpoint(transfer.square_change(pairs, arb(-7))))

    def test_full_line_price_dominates_known_two_sided_integral(self):
        pairs = [[arb(1), arb(1)]] * 4
        result = transfer.full_line_charge(pairs)
        exact_integral = 120 / (7 * arb.pi())
        total = transfer.lift(Fraction(result["total_upper"]["upper_exact"]))
        self.assertTrue(total > exact_integral)
        cutoff = transfer.lift(Fraction(result["tail_t_cutoff_exact"]))
        exact_tail = 15 / (7 * arb.pi() * cutoff**7)
        tail = transfer.lift(Fraction(result["tail_upper"]["upper_exact"]))
        self.assertTrue(tail >= exact_tail.upper())

    def test_zero_delta_has_zero_full_line_change(self):
        pairs = [[arb(2), arb(3)], [arb(4), arb(5)], [arb(0), arb(0)], [arb(0), arb(0)]]
        result = transfer.full_line_charge(pairs)
        self.assertEqual(result["total_upper"]["upper_exact"], "0")

    def test_source_hash_mutation_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "input.json"
            path.write_text("source")
            correct = transfer.hashlib.sha256(path.read_bytes()).hexdigest()
            self.assertEqual(transfer.check_hash(path, correct), correct)
            path.write_text("mutated")
            with self.assertRaises(ValueError):
                transfer.check_hash(path, correct)


if __name__ == "__main__":
    unittest.main()

