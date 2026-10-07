"""Exact algebra, independent degree-48 enclosure, and rejected certificate drift."""
from fractions import Fraction
import unittest
from unittest.mock import patch

from flint import arb, ctx, fmpq

from analytic_moment_residual_probe_2619 import build_panel
from generate_moment_panel_certificate_2621 import (
    ROOT, add, derivative, evaluate, generated_sources, multiply, panel_data, payload_data, scale,
)
from generate_moment_scalar_certificate_2620 import compact_scalar
from validate_moment_panel_certificate_2621 import check_inputs


def exact(value):
    return Fraction(str(value))


def ball(value):
    value = Fraction(value)
    return arb(fmpq(value.numerator, value.denominator))


class PanelCertificateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        ctx.prec = 512
        cls.data = panel_data()
        cls.center, cls.half_width = Fraction(9, 200), Fraction(1, 200)

    def test_recurrence_matches_independent_flint_engine(self):
        reference = build_panel(fmpq(str(self.data["beta"])), fmpq(9, 200), fmpq(1, 200), 32)
        self.assertEqual(self.data["coefficients"], list(map(exact, reference["coefficients"])) + [0])
        self.assertEqual(self.data["residual"][:37], list(map(exact, reference["residual"])))

    def test_derivative_matches_indexed_coefficients(self):
        coefficients = self.data["coefficients"]
        expected = [index * value for index, value in enumerate(coefficients) if index] + [0]
        self.assertEqual(derivative(coefficients), expected)
        self.assertEqual(derivative(self.data["primitive"]), coefficients)

    def test_integral_matches_symmetric_power_sum(self):
        expected = sum(2 * value * self.half_width ** (index + 1) / (index + 1)
                       for index, value in enumerate(self.data["coefficients"]) if index % 2 == 0)
        self.assertEqual(expected, self.data["integral"])

    def test_residual_reconstructs_equation_at_signed_points(self):
        for position in (-self.half_width, -self.half_width / 3, Fraction(0),
                         self.half_width / 3, self.half_width):
            denominator = (1 - (self.center + position) ** 2) ** 2
            numerator = self.data["beta"] * denominator - 60 * (self.center + position)
            polynomial = sum(value * position ** index
                             for index, value in enumerate(self.data["coefficients"]))
            differential = sum(index * value * position ** (index - 1)
                               for index, value in enumerate(self.data["coefficients"]) if index)
            self.assertEqual(evaluate(position, self.data["residual"]),
                             denominator * differential - numerator * polynomial)

    def test_only_five_residual_coefficients_are_nonzero(self):
        self.assertEqual(self.data["residual"][:32], [0] * 32)
        self.assertEqual(self.data["residual"][37:], [0])
        self.assertTrue(all(value != 0 for value in self.data["residual"][32:37]))

    def test_residual_bound_encloses_signed_samples(self):
        for numerator in range(-10, 11):
            position = self.half_width * Fraction(numerator, 10)
            self.assertLessEqual(abs(evaluate(position, self.data["residual"])), self.data["residual_upper"])

    def test_coefficient_perturbation_breaks_low_order_residual(self):
        coefficients = list(self.data["coefficients"])
        coefficients[32] += 1
        deficit = [1 - self.center ** 2, -2 * self.center, Fraction(-1)]
        denominator = multiply(deficit, deficit)
        numerator = add(scale(self.data["beta"], denominator), [-60 * self.center, Fraction(-60)])
        residual = add(multiply(denominator, derivative(coefficients)),
                       scale(-1, multiply(numerator, coefficients)))
        self.assertNotEqual(residual[31], 0)

    def test_primitive_perturbation_breaks_derivative_replay(self):
        primitive = list(self.data["primitive"])
        primitive[1] += 1
        self.assertNotEqual(derivative(primitive), self.data["coefficients"])

    def test_unequal_length_polynomial_arithmetic(self):
        self.assertEqual(add([1, 2], [3, 4, 5]), [4, 6, 5])
        self.assertEqual(multiply([1, 2], [3, 4, 5]), [3, 10, 13, 10])
        self.assertEqual(multiply([], [1, 2]), [])
        self.assertEqual(derivative([1, 2, 3]), [2, 6, 0])

    def test_degree48_control_is_inside_certified_panel_radius(self):
        reference = build_panel(fmpq(str(self.data["beta"])), fmpq(9, 200), fmpq(1, 200), 48)
        amplitude = ball(self.data["phase"]).exp()
        center = ball(self.data["radius"]) * amplitude * ball(exact(reference["integral_polynomial"]))
        error = ball(self.data["radius"]) * amplitude * ball(2 * self.half_width ** 2) * (
            ball(exact(reference["residual_quotient"])) *
            (2 * ball(exact(reference["phase_variation"]))).exp())
        deviation = abs(center - ball(self.data["integral_center"])) + error
        self.assertTrue(deviation < ball(self.data["integral_charge"]))

    def test_physical_multiplier_and_final_charge_are_retained(self):
        amplitude, radius = compact_scalar(self.data["phase"])[-1]
        self.assertEqual(self.data["integral_center"], self.data["radius"] * amplitude * self.data["integral"])
        self.assertGreaterEqual(self.data["integral_charge"],
                                self.data["radius"] * radius * abs(self.data["integral"]))
        self.assertGreater(self.data["integral_charge"], 0)
        self.assertLessEqual(self.data["integral_charge"], Fraction(1, 10 ** 82))

    def test_generated_sources_and_payload_are_current(self):
        self.assertEqual(generated_sources(self.data), generated_sources(panel_data()))
        check_inputs()
        self.assertNotIn(b"\r\n", (ROOT / "results/2621_moment_panel_payload.json").read_bytes())
        payload = payload_data(self.data)
        self.assertFalse(payload["lean_verified"])
        self.assertFalse(payload["actual_entry_containment_lean_verified"])
        self.assertFalse(payload["producer_go"])
        self.assertFalse(payload["rh_claim"])

    def test_generated_source_drift_is_rejected(self):
        sources = generated_sources(self.data)
        sources[next(iter(sources))] += "\n"
        with patch("validate_moment_panel_certificate_2621.generated_sources", return_value=sources):
            with self.assertRaisesRegex(ValueError, "generated source drift"):
                check_inputs()

    def test_payload_scope_drift_is_rejected(self):
        payload = payload_data(self.data)
        payload["lean_verified"] = True
        with patch("validate_moment_panel_certificate_2621.payload_data", return_value=payload):
            with self.assertRaisesRegex(ValueError, "payload or fingerprint drift"):
                check_inputs()


if __name__ == "__main__":
    unittest.main()
