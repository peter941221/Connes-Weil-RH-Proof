"""2295 controls for direct signed-functional differences."""
import json
import unittest
from unittest.mock import patch

import numpy as np
import mpmath as mp

import routea_direct_functional_difference_screen_2295 as instrument


class DirectFunctionalDifferenceControls(unittest.TestCase):
    def test_small_frequency_moments_against_independent_integral(self):
        mp.mp.dps = 60
        for alpha in (-1.01, -1.0, -0.03, -1e-11, 0.0, 1e-11, 0.03, 1.0, 1.01):
            moments = instrument.filon.polynomial_moments(alpha, 6)
            for index, computed in enumerate(moments):
                truth = mp.quad(lambda point: point**index*mp.exp(-1j*mp.mpf(alpha)*point), [-1, 1])
                self.assertLess(abs(computed-complex(truth)), 2e-12)

    def test_composite_gl_on_independent_constant_amplitude_integral(self):
        xi = np.array([-2.0, -0.1, 0.0, 0.1, 2.0])
        amplitude = 2-3j
        with patch.object(instrument.filon, "owner_values", side_effect=lambda nodes, families, coefficients:
                          np.full_like(nodes, amplitude, dtype=complex)):
            values = instrument.reference_transform(xi, [(1.0, 0.0)], [1+0j], 4, 32)
        expected = 2*amplitude*np.sinc(2*xi)
        np.testing.assert_allclose(values, expected, atol=1e-13, rtol=1e-13)

    def test_signed_kernel_and_full_complex_polynomial_modulus(self):
        xi = np.array([-1.0, 0.0, 1.0])
        with patch.object(instrument.filon, "annihilator", return_value=np.full(3, 3+4j)):
            values = instrument.functional(xi, np.full(3, 3+4j), np.ones(3, complex),
                                           np.array([-2.0, 0.0, 2.0]))
        np.testing.assert_array_equal(values, [-1250.0, 0.0, 1250.0])

    def test_identical_transforms_give_exact_zero_difference(self):
        xi = np.array([-1.0, 0.0, 1.0])
        base = np.array([1+2j, 2-1j, 3+1j])
        corr = np.array([-2+1j, 4+1j, 1-3j])
        kernel = np.array([-2.0, 3.0, -1.0])
        first = instrument.functional(xi, base, corr, kernel)
        second = instrument.functional(xi, base.copy(), corr.copy(), kernel)
        np.testing.assert_array_equal(first-second, np.zeros(3))

    def test_artifact_has_two_signs_complete_owner_and_both_grid_steps(self):
        artifact = json.loads(instrument.OUT.read_text(encoding="utf-8"))
        self.assertFalse(artifact["certificate"])
        self.assertFalse(artifact["hgap_closed"])
        self.assertEqual({row["xi_step"] for row in artifact["rows"]}, {0.02, 0.01})
        for row in artifact["rows"]:
            self.assertEqual(row["prime_power_count"], 41136)
            self.assertGreater(row["direct_absolute_difference"], abs(row["direct_signed_difference"])*0.9999999999)
            self.assertTrue(np.isfinite(row["direct_absolute_difference"]))

    def test_reference_movement_is_recorded_not_an_integral_certificate(self):
        artifact = json.loads(instrument.OUT.read_text(encoding="utf-8"))
        for step in (0.02, 0.01):
            rows = [row for row in artifact["rows"] if row["degree"] == 4 and row["xi_step"] == step]
            self.assertEqual({row["nodes_per_panel"] for row in rows}, {256, 512})
            first, second = rows
            difference = abs(first["direct_signed_difference"]-second["direct_signed_difference"])
            self.assertLess(difference/max(abs(second["direct_signed_difference"]), 1), 1e-8)
        self.assertFalse(artifact["certificate"])


if __name__ == "__main__":
    unittest.main()
