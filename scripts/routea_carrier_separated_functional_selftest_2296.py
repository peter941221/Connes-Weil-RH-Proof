"""2296 carrier-identity, phase-sign, moments and same-owner controls."""
import json
from fractions import Fraction
import unittest
from unittest.mock import patch

import mpmath as mp
import numpy as np

import routea_carrier_separated_functional_screen_2296 as screen


class CarrierSeparatedControls(unittest.TestCase):
    def test_grouping_preserves_every_family_index(self):
        _, families, _, _ = screen.SOURCE.load_owner()
        groups = screen.carrier_groups(families)
        self.assertEqual(len(groups), 25)
        self.assertEqual(sorted(index for _, indices in groups for index in indices), list(range(30)))
        for theta, indices in groups:
            self.assertTrue(all(families[index][1] == theta for index in indices))

    def test_envelope_sum_reconstructs_stored_owner(self):
        _, families, base, correction = screen.SOURCE.load_owner()
        control = screen.identity_control(families, np.column_stack((base, correction)))
        self.assertTrue(control["passed"])
        self.assertLessEqual(control["allowance_ratio"], 1)

    def test_exterior_profile_is_zero(self):
        coordinates = np.array([-2.0, -1.0, 1.0, 2.0])
        values = screen.envelope_values(coordinates, [(1.0, 8.0)], np.array([2-3j]), [0])
        np.testing.assert_array_equal(values, np.zeros((4, 1)))

    def test_invalid_coefficient_length_is_rejected(self):
        with self.assertRaises(ValueError):
            screen.envelope_values(np.array([0.0]), [(1.0, 0.0)], np.array([], complex), [0])

    def test_bulk_moments_against_independent_integral_both_branches(self):
        mp.mp.dps = 60
        alpha = np.array([-80, -8, -2.01, -2, -0.03, -1e-11, 0, 1e-11, 0.03, 2, 2.01, 8, 80])
        moments = screen.moment_matrix(alpha, 6)
        for row, frequency in enumerate(alpha):
            for degree in range(7):
                truth = mp.quad(lambda coordinate: coordinate**degree*mp.exp(-1j*mp.mpf(float(frequency))*coordinate), [-1, 1])
                self.assertLess(abs(moments[row, degree]-complex(truth)), 2e-12)

    def test_carrier_shift_sign_and_zero_shift_on_known_integral(self):
        theta = 7.0
        coefficients = np.array([[2-3j, -1+2j]])
        xi = np.array([-2, -0.1, 0, theta/(2*np.pi), 2])
        with patch.object(screen, "envelope_values", side_effect=lambda coordinates, families, coefficients, indices:
                          np.tile(coefficients[0], (len(coordinates), 1))):
            values = screen.separated_transform(xi, [(1.0, theta)], coefficients, 4, 4)
        expected = 2*np.sinc(2*xi-theta/np.pi)[:, None]*coefficients
        np.testing.assert_allclose(values, expected, rtol=1e-12, atol=1e-12)

    def test_grouped_complex_cancellation_is_not_replaced_by_moduli(self):
        xi = np.array([-2.0, 0.0, 2.0])
        families = [(1.0, 7.0), (1.0, 7.0)]
        coefficients = np.array([2-3j, -2+3j])
        values = screen.separated_transform(xi, families, coefficients, 4, 4)
        np.testing.assert_array_equal(values, np.zeros((3, 1)))

    def test_zero_channel_and_exterior_panels_keep_fixed_polynomial_shape(self):
        xi = np.array([-2.0, 0.0, 2.0])
        families = [(1.0, 7.0), (2.0, -1.0)]
        coefficients = np.array([[0+0j, 2-3j], [0+0j, 0+0j]])
        values = screen.separated_transform(xi, families, coefficients, 8, 4)
        self.assertEqual(values.shape, (3, 2))
        np.testing.assert_array_equal(values[:, 0], np.zeros(3))
        self.assertTrue(np.all(np.isfinite(values[:, 1])))

    def test_cross_carrier_contributions_remain_complex_until_final_sum(self):
        xi = np.array([0.0])
        families = [(1.0, -2.0), (1.0, 2.0)]
        coefficients = np.array([[1+0j], [-1+0j]])
        with patch.object(screen, "envelope_values", side_effect=lambda coordinates, families, coefficients, indices:
                          np.tile(coefficients[indices[0]], (len(coordinates), 1))):
            values = screen.separated_transform(xi, families, coefficients, 4, 4)
        np.testing.assert_allclose(values, np.zeros((1, 1)), atol=1e-14)

    def test_artifact_preserves_scope_and_same_run_baseline(self):
        artifact = json.loads(screen.OUT.read_text(encoding="utf-8"))
        self.assertFalse(artifact["certificate"])
        self.assertFalse(artifact["hgap_closed"])
        self.assertEqual(artifact["owner"]["prime_power_count"], 41136)
        self.assertEqual(artifact["owner"]["family_count"], 30)
        for control in artifact["baseline_controls"]:
            if control["xi_step"] in (0.02, 0.01):
                self.assertTrue(control["historical_row_available"])
                self.assertLessEqual(control["relative_movement"], 1e-10)
            else:
                self.assertEqual(control["xi_step"], 0.005)
                self.assertFalse(control["historical_row_available"])
        self.assertEqual({row["xi_step"] for row in artifact["rows"]}, {0.02, 0.01, 0.005})
        self.assertEqual({row["reference_order"] for row in artifact["rows"]}, {256, 512})
        for row in artifact["rows"]:
            self.assertTrue(np.isfinite(row["direct_signed_difference"]))
            self.assertGreaterEqual(row["direct_absolute_difference"], abs(row["direct_signed_difference"])*0.9999999999)

    def test_degree_six_lobatto_integral_is_exact(self):
        primitive = lambda square: (square**4/Fraction(8)-square**3/Fraction(3)
            +Fraction(19, 64)*square**2-Fraction(3, 32)*square)
        integral = 2*(2*primitive(Fraction(3, 4))-2*primitive(Fraction(1, 4))-primitive(Fraction(1)))
        self.assertEqual(integral, Fraction(1, 32))

    def test_profile_summaries_gate_every_grid_and_reference(self):
        artifact = json.loads(screen.OUT.read_text(encoding="utf-8"))
        for summary in artifact["profile_summaries"]:
            rows = [row for row in artifact["rows"] if row["panels"] == summary["panels"]
                    and row["degree"] == summary["degree"]]
            self.assertEqual(len(rows), 6)
            self.assertEqual(summary["signed_diagnostic_pass_all_controls"],
                             all(abs(row["direct_signed_difference"]) <= 1e7 for row in rows))
            self.assertEqual(summary["absolute_diagnostic_pass_all_controls"],
                             all(row["direct_absolute_difference"] <= 1e7 for row in rows))


if __name__ == "__main__":
    unittest.main()
