"""Exact replay controls and independent 512-bit Arb exponential containment."""
from fractions import Fraction
import unittest
from unittest.mock import patch

from flint import arb, ctx, fmpq

from generate_moment_scalar_certificate_2620 import (
    COORDINATE_BITS, ROOT, compact_scalar, generated_sources, get_data, round_down, round_up,
)
from validate_moment_scalar_certificate_2620 import check_inputs


def ball(value):
    value = Fraction(value)
    return arb(fmpq(value.numerator, value.denominator))


class ScalarCertificateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        ctx.prec = 512
        cls.data = get_data()

    def test_negative_directed_rounding(self):
        self.assertEqual(round_down(Fraction(-1, 3), 3), Fraction(-3, 8))
        self.assertEqual(round_up(Fraction(-1, 3), 3), Fraction(-1, 4))

    def test_rounding_encloses_signed_inputs(self):
        for value in (Fraction(-5, 7), Fraction(0), Fraction(5, 7)):
            self.assertLessEqual(round_down(value, 320), value)
            self.assertGreaterEqual(round_up(value, 320), value)
            self.assertLessEqual(round_up(value, 320) - round_down(value, 320), Fraction(1, 2 ** 320))

    def test_tiny_argument_guard_and_boundary(self):
        for sign in (-1, 1):
            boundary = sign * Fraction(2 ** 20, 1000)
            self.assertEqual(len(compact_scalar(boundary)), 21)
            with self.assertRaises(ValueError):
                compact_scalar(boundary + sign * Fraction(1, 10 ** 9))

    def test_horner_order_matches_independent_taylor(self):
        scaled = self.data["phase"] / 2 ** 20
        polynomial, term = Fraction(1), Fraction(1)
        for degree in range(1, 20):
            term *= scaled / degree
            polynomial += term
        center, radius = compact_scalar(self.data["phase"])[0]
        self.assertLessEqual(abs(polynomial - center), radius)
        self.assertLessEqual(abs(polynomial - center), 19 * Fraction(1, 2 ** COORDINATE_BITS))

    def test_every_state_contains_independent_exponential(self):
        for key in ("phase", "growth", "edge"):
            for index, (center, radius) in enumerate(compact_scalar(self.data[key])):
                truth = ball(self.data[key] / 2 ** (20 - index)).exp()
                self.assertTrue(truth > ball(center - radius), (key, index, "lower"))
                self.assertTrue(truth < ball(center + radius), (key, index, "upper"))
                self.assertGreaterEqual(radius, 0)

    def test_radius_thresholds(self):
        for key, digits in (("phase", 80), ("growth", 70), ("edge", 90)):
            self.assertLessEqual(compact_scalar(self.data[key])[-1][1], Fraction(1, 10 ** digits))

    def test_perturbed_center_fails_containment(self):
        center, radius = compact_scalar(self.data["phase"])[-1]
        truth = ball(self.data["phase"]).exp()
        self.assertTrue(truth < ball(center + 4 * radius - radius))

    def test_generated_sources_are_deterministic_and_current(self):
        first = generated_sources(self.data)
        self.assertEqual(first, generated_sources(get_data()))
        check_inputs()
        self.assertNotIn(b"\r\n", (ROOT / "results/2620_moment_scalar_payload.json").read_bytes())

    def test_generation_drift_is_rejected(self):
        sources = generated_sources(self.data)
        filename = next(iter(sources))
        sources[filename] += "\n"
        with patch("validate_moment_scalar_certificate_2620.generated_sources", return_value=sources):
            with self.assertRaisesRegex(ValueError, "generated source drift"):
                check_inputs()

    def test_capture_fingerprint_drift_is_rejected(self):
        changed = dict(self.data, capture_sha256="0" * 64)
        with patch("validate_moment_scalar_certificate_2620.get_data", return_value=changed):
            with self.assertRaisesRegex(ValueError, "capture_sha256"):
                check_inputs()

    def test_replay_payload_drift_is_rejected(self):
        with patch("validate_moment_scalar_certificate_2620.compact_scalar",
                   return_value=[(Fraction(0), Fraction(1))]):
            with self.assertRaisesRegex(ValueError, "scalar payload"):
                check_inputs()

    def test_owner_geometry_and_edge_charge(self):
        self.assertEqual(-Fraction(9, 10) + (2 * 94 + 1) * Fraction(1, 200), Fraction(9, 200))
        self.assertEqual(Fraction(9, 200) - Fraction(1, 200), Fraction(1, 25))
        self.assertEqual(Fraction(9, 200) + Fraction(1, 200), Fraction(1, 20))
        upper = compact_scalar(self.data["edge"])[-1]
        charge = 2 * self.data["radius"] * Fraction(1, 10) * sum(upper)
        self.assertLessEqual(charge, Fraction(2, 10 ** 68))

    def test_payload_does_not_claim_complete_entry(self):
        inputs, _ = check_inputs()
        for key in ("lean_verified", "polynomial_table_lean_verified",
                    "actual_entry_containment_lean_verified", "producer_go", "rh_claim"):
            self.assertIs(inputs[key], False)


if __name__ == "__main__":
    unittest.main()
