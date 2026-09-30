"""Independent derivative, cell coverage and artifact controls for 2302."""
import hashlib
import json
import math
from fractions import Fraction
import unittest

import mpmath as mp
import numpy as np

import routea_local_frequency_taylor_screen_2302 as screen


class LocalFrequencyControls(unittest.TestCase):
    def setUp(self):
        mp.mp.dps = 100
        mp.iv.dps = 80
        self.owner = screen.evaluator.bridge.refined.remainder.jets.repaired
        self.pi_value = screen.evaluator.midpoint_extended(mp.iv.pi)
        self.series = screen.generalized_series(12)
        coefficients = np.zeros((2, 2, 7, 2), dtype=complex)
        coefficients[:, :, 0, :] = np.array([1+2j, -2+1j])
        coefficients[:, :, 1, :] = np.array([2-1j, 1+3j])
        coefficients[:, :, 2, :] = np.array([-1+1j, 2-2j])
        self.model = {'theta': [-4.0, 3.0], 'panels': 2,
                      'centers': np.array([-1.0, 1.0], dtype=screen.evaluator.LD),
                      'radius': screen.evaluator.LD('0.005'), 'coefficients': coefficients}
        self.totals = {}
        for channel_index, channel in enumerate(('base', 'corr')):
            mass = mp.iv.mpf(0)
            for group in range(2):
                for panel in range(2):
                    mass += screen.evaluator.exact_extended(self.model['radius'])*sum(
                        (mp.iv.mpf(2)/(degree+1)*abs(mp.iv.mpc(float(value.real), float(value.imag)))
                         for degree, value in enumerate(coefficients[group, panel, :, channel_index])), mp.iv.mpf(0))
            self.totals[channel] = {'mass': mass}

    def exact_complex(self, value):
        return mp.mpc(self.owner.lower(screen.evaluator.exact_extended(value.real)),
                      self.owner.lower(screen.evaluator.exact_extended(value.imag)))

    def test_generalized_moments_both_parities_against_quad(self):
        alpha = np.array([-3, 0, 3], dtype=screen.evaluator.LD)
        values = screen.generalized_moments(alpha, self.series, 12)
        _, constants = screen.evaluator.arithmetic_price(self.model, self.totals, self.pi_value)
        allowance = mp.mpf(constants['moment_relative_error']['upper'])
        for index, argument in enumerate(alpha):
            exact = self.owner.lower(screen.evaluator.exact_extended(argument))
            for degree in range(13):
                truth = mp.quad(lambda coordinate: coordinate**degree*mp.exp(-1j*exact*coordinate), [-1, 0, 1])
                self.assertLessEqual(abs(self.exact_complex(values[index, degree])-truth), allowance*2/(degree+1))
                self.assertEqual(values[index, degree].real if degree % 2 else values[index, degree].imag, 0)
        with self.assertRaises(ValueError):
            screen.generalized_moments(np.array([3.1], dtype=screen.evaluator.LD), self.series, 12)

    def test_y_power_polynomials_against_exact_product(self):
        table = screen.derivative_polynomials(self.model, 6)
        radius = self.owner.lower(screen.evaluator.exact_extended(self.model['radius']))
        unit = mp.mpf(2)**-64
        for order in range(7):
            for panel in range(2):
                center = mp.mpf(float(self.model['centers'][panel]))
                for coordinate in (mp.mpf('-0.5'), mp.mpf(0), mp.mpf('0.5')):
                    for channel in range(2):
                        base = [mp.mpc(float(value.real), float(value.imag)) for value in self.model['coefficients'][0, panel, :, channel]]
                        truth = (center+radius*coordinate)**order*sum((value*coordinate**degree for degree, value in enumerate(base)), mp.mpc(0))
                        computed = sum((self.exact_complex(value)*coordinate**degree for degree, value in enumerate(table[order, 0, panel, :, channel])), mp.mpc(0))
                        count = 8*order
                        allowance = count*unit/(1-count*unit)*(abs(center)+radius)**order*sum(abs(value) for value in base)
                        self.assertLessEqual(abs(computed-truth), allowance)

    def test_derivative_execution_against_independent_reference(self):
        points = np.array([-1.0, 0.0, 1.0])
        orders = (0, 1, 3, 6)
        table = screen.derivative_polynomials(self.model, 6)
        computed = screen.evaluate_derivatives(self.model, points, self.pi_value, self.series, table)
        truth = screen.independent_derivative_reference(self.model, points, orders)
        errors, _, _ = screen.derivative_error_bounds(self.model, self.totals, self.pi_value, 6)
        baseline, _ = screen.evaluator.evaluate(self.model, points, self.pi_value, self.series[:9])
        self.assertTrue(np.array_equal(computed[0], baseline))
        for position, order in enumerate(orders):
            for index in range(3):
                for channel_index, channel in enumerate(('base', 'corr')):
                    value = mp.mpc(float(computed[order, index, channel_index].real), float(computed[order, index, channel_index].imag))
                    self.assertLessEqual(abs(value-truth[position][index][channel_index]), self.owner.lower(errors[channel][order]))

    def test_cell_suprema_contains_between_node_values(self):
        center = np.array([0.2])
        table = screen.derivative_polynomials(self.model, 6)
        jets = screen.evaluate_derivatives(self.model, center, self.pi_value, self.series, table)
        errors, support, _ = screen.derivative_error_bounds(self.model, self.totals, self.pi_value, 6)
        radius = mp.iv.mpf('0.01')
        remainder = screen.taylor_remainders(self.totals, support, radius, 6)
        upper = screen.cell_suprema(jets, errors, remainder, radius)[0]
        truth = screen.independent_derivative_reference(self.model, np.array([0.19, 0.2, 0.21]), (0,))
        for row in truth[0]:
            for channel in range(2):
                self.assertLessEqual(abs(row[channel]), mp.mpf(float(upper[channel])))

    def test_rational_cells_cover_both_endpoints(self):
        step = 0.02
        centers = -40+(np.arange(4000)+0.5)*step
        radius, _ = screen.coverage_radius(step, centers)
        bound = self.owner.lower(radius)
        rational = Fraction('0.02')
        for index in (0, 1, 1999, 2000, 3999):
            for endpoint in (-40+rational*index, -40+rational*(index+1)):
                distance = abs(Fraction.from_float(float(centers[index]))-endpoint)
                self.assertLessEqual(mp.mpf(distance.numerator)/distance.denominator, bound)
        with self.assertRaises(ValueError):
            screen.coverage_radius(step, centers[:-1])

    def test_norm_is_taken_after_complex_sum(self):
        jets = np.zeros((7, 1, 2), dtype=complex)
        jets[0, 0, :] = [1j, -1j]
        errors = {channel: [mp.iv.mpf(0) for _ in range(7)] for channel in ('base', 'corr')}
        remainder = {channel: mp.iv.mpf(0) for channel in errors}
        bounds = screen.cell_suprema(jets, errors, remainder, mp.iv.mpf('0.01'))
        self.assertTrue(np.all(bounds >= 1))
        self.assertTrue(np.all(bounds < 1.000000000001))

    def test_artifact_scope_and_controls(self):
        artifact = json.loads(screen.OUT.read_text(encoding='utf-8'))
        self.assertFalse(artifact['certificate'])
        self.assertFalse(artifact['hgap_closed'])
        self.assertEqual(artifact['owner']['family_count'], 30)
        self.assertTrue(artifact['order_zero_bitwise_control'])
        self.assertEqual(len(artifact['independent_controls']), 24)
        self.assertEqual({row['order'] for row in artifact['independent_controls']}, {0, 1, 3, 6})
        self.assertTrue(all(row['allowance_ratio'] <= 1 for row in artifact['independent_controls']))
        for row in artifact['rows']:
            self.assertEqual(row['prime_power_count'], 41136)
            self.assertEqual(row['cell_count'], round(80/row['xi_step']))
            self.assertEqual(row['sampled_weight_proxy_budget_ratio'], row['sampled_weight_proxy_charge']/1e7)
            self.assertGreaterEqual(row['sampled_weight_proxy_charge'], 0)

    def test_source_provenance(self):
        artifact = json.loads(screen.OUT.read_text(encoding='utf-8'))
        for name, expected in artifact['source_sha256'].items():
            self.assertEqual(hashlib.sha256((screen.ROOT/name).read_bytes()).hexdigest(), expected)


if __name__ == '__main__':
    unittest.main()
