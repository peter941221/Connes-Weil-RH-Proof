"""Independent formula and support controls for the repaired 2292 instrument."""
import unittest

import mpmath as mp

import routea_interval_fifth_derivative_preflight_2292 as instrument


def reference(coordinate, families, coefficients):
    total = mp.mpc(0)
    for coefficient, (width, theta) in zip(coefficients, families):
        radius = mp.mpf(width)**2
        if abs(coordinate) < radius:
            quotient = 1 - (coordinate/radius)**2
            total += mp.mpc(float(coefficient.real), float(coefficient.imag))*mp.exp(
                -30/quotient + mp.mpc(0.5, theta)*coordinate)
    return total


class FifthDerivativeControls(unittest.TestCase):
    def setUp(self):
        mp.mp.dps = 100
        mp.iv.dps = 70

    def assert_contains(self, box, truth):
        self.assertLessEqual(instrument.lower(box.real), truth.real)
        self.assertGreaterEqual(instrument.upper(box.real), truth.real)
        self.assertLessEqual(instrument.lower(box.imag), truth.imag)
        self.assertGreaterEqual(instrument.upper(box.imag), truth.imag)

    def test_single_family_both_parities_against_independent_diff(self):
        families = [(1.6, -39.25244858548658)]
        coefficients = [complex(2.0, -3.0)]
        for point in (-2, -0.25, 0, 0.25, 2):
            with self.subTest(point=point):
                coordinate = mp.mpf(point)
                box = instrument.owner_fifth_iv(mp.iv.mpf(coordinate), families, coefficients)
                truth = mp.diff(lambda value: reference(value, families, coefficients), coordinate, 5)
                self.assert_contains(box, truth)

    def test_grouped_stored_owner_against_independent_diff(self):
        _, families, base, correction = instrument.owner_source.load_owner()
        for channel, coefficients in (("base", base), ("corr", correction)):
            for point in (-5, -2, 0, 2, 5):
                with self.subTest(channel=channel, point=point):
                    coordinate = mp.mpf(point)
                    box = instrument.owner_fifth_iv(mp.iv.mpf(coordinate), families, coefficients)
                    truth = mp.diff(lambda value: reference(value, families, coefficients), coordinate, 5)
                    self.assert_contains(box, truth)

    def test_outside_support_is_identically_zero(self):
        box = instrument.owner_fifth_iv(mp.iv.mpf([3, 4]), [(1.6, 0.0)], [1+0j])
        self.assertEqual(instrument.modulus_upper(box), 0)

    def test_edge_crossing_is_explicitly_unresolved(self):
        with self.assertRaises(instrument.SupportEdgeError):
            instrument.owner_fifth_iv(mp.iv.mpf([2.5, 2.6]), [(1.6, 0.0)], [1+0j])

    def test_modulus_includes_both_channels(self):
        self.assertEqual(instrument.modulus_upper(mp.iv.mpc(3, 4)), 5)

    def test_finite_width_cell_contains_independent_samples(self):
        families = [(1.6, -4.0), (2.0, 6.0)]
        coefficients = [2-3j, -1+2j]
        box = instrument.owner_fifth_iv(mp.iv.mpf([0.1, 0.2]), families, coefficients)
        for point in (0.1, 0.15, 0.2):
            coordinate = mp.mpf(point)
            truth = mp.diff(lambda value: reference(value, families, coefficients), coordinate, 5)
            self.assert_contains(box, truth)

    def test_length_mismatch_is_rejected(self):
        with self.assertRaises(ValueError):
            instrument.owner_fifth_iv(mp.iv.mpf(0), [(1.6, 0.0)], [])


if __name__ == "__main__":
    unittest.main()
