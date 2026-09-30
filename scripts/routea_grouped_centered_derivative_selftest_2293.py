"""Independent controls for the 2293 jet and flat-endpoint envelopes."""
import math
import unittest

import mpmath as mp

import routea_grouped_centered_derivative_preflight_2293 as instrument
from routea_interval_fifth_derivative_selftest_2292 import reference
from routea_interval_fifth_derivative_selftest_2292 import FifthDerivativeControls


class CenteredDerivativeControls(FifthDerivativeControls):
    def test_jet_fifth_agrees_with_explicit_interval_formula(self):
        families = [(1.6, -39.25244858548658)]
        coefficients = [2-3j]
        for point in (-2, -0.5, 0, 0.5, 2):
            coordinate = mp.iv.mpf(point)
            jet, _ = instrument.grouped_derivative(coordinate, families, coefficients, 5)
            truth = mp.diff(lambda value: reference(value, families, coefficients), mp.mpf(point), 5)
            self.assert_contains(jet, truth)

    def test_sixth_grouped_jet_both_parities(self):
        _, families, base, correction = instrument.repaired.owner_source.load_owner()
        for coefficients in (base, correction):
            for point in (-5, -2, 0, 2, 5):
                coordinate = mp.iv.mpf(point)
                jet, _ = instrument.grouped_derivative(coordinate, families, coefficients, 6)
                truth = mp.diff(lambda value: reference(value, families, coefficients), mp.mpf(point), 6)
                self.assert_contains(jet, truth)

    def test_edge_envelope_both_sides_fifth_and_sixth(self):
        width = 1.6
        radius = mp.mpf(width)**2
        families = [(width, -39.25244858548658)]
        coefficients = [2-3j]
        for sign in (-1, 1):
            endpoints = sorted((sign*(radius - mp.mpf("0.03")), sign*(radius + mp.mpf("0.01"))))
            box = mp.iv.mpf(endpoints)
            for order in (5, 6):
                jet, edges = instrument.grouped_derivative(box, families, coefficients, order)
                self.assertEqual(edges, 1)
                for fraction in (mp.mpf("0.1"), mp.mpf("0.5"), mp.mpf("0.9")):
                    point = sign*(radius - mp.mpf("0.03")*fraction)
                    truth = mp.diff(lambda value: reference(value, families, coefficients), point, order)
                    self.assert_contains(jet, truth)

    def test_centered_variation_contains_grid(self):
        families = [(1.6, -4.0), (2.0, 6.0)]
        coefficients = [2-3j, -1+2j]
        box = mp.iv.mpf([0.1, 0.2])
        center = (box.a + box.b)/2
        radius = (box.b - box.a)/2
        value, _ = instrument.grouped_derivative(center, families, coefficients, 5)
        sixth, _ = instrument.grouped_derivative(box, families, coefficients, 6)
        bound = instrument.repaired.upper(abs(value) + radius*abs(sixth))
        for point in (0.1, 0.15, 0.2):
            truth = mp.diff(lambda coordinate: reference(coordinate, families, coefficients), mp.mpf(point), 5)
            self.assertLessEqual(abs(truth), bound)

    def test_lobatto_product_integral(self):
        product = lambda value: value*(value**2 - 1)*(value**2 - mp.mpf("0.5"))
        integral = mp.quad(lambda value: abs(product(value)),
                           [-1, -mp.sqrt(mp.mpf("0.5")), 0, mp.sqrt(mp.mpf("0.5")), 1])
        self.assertLess(abs(integral - mp.mpf(1)/8), mp.mpf("1e-90"))


if __name__ == "__main__":
    unittest.main()
