"""Independent execution, parity, accumulation and artifact controls for 2301."""
import hashlib
import json
import math
import unittest

import mpmath as mp
import numpy as np

import routea_regenerated_carrier_evaluator_2301 as screen


class RegeneratedEvaluatorControls(unittest.TestCase):
    def setUp(self):
        mp.mp.dps = 100
        mp.iv.dps = 80
        self.owner = screen.bridge.refined.remainder.jets.repaired
        self.coefficients, _ = screen.series_coefficients()
        self.pi_value = screen.midpoint_extended(mp.iv.pi)

    def exact_complex(self, value):
        return mp.mpc(self.owner.lower(screen.exact_extended(value.real)),
                      self.owner.lower(screen.exact_extended(value.imag)))

    def dummy_price(self, pi_value):
        model = {'theta': [79.0], 'centers': np.array([-6.55, 6.55], dtype=screen.LD),
                 'radius': screen.LD('0.008'), 'panels': 768}
        totals = {'base': {'mass': mp.iv.mpf(1)}, 'corr': {'mass': mp.iv.mpf(2)}}
        return screen.arithmetic_price(model, totals, pi_value)

    def test_platform_and_exact_extended_lift(self):
        self.assertEqual(screen.platform_contract()['significand_bits'], 64)
        value = screen.LD(1)/screen.LD(3)
        numerator, denominator = value.as_integer_ratio()
        box = screen.exact_extended(value)
        self.assertEqual(self.owner.lower(box), mp.mpf(numerator)/denominator)
        self.assertEqual(self.owner.lower(box), self.owner.upper(box))

    def test_phase_series_against_independent_exp_both_signs(self):
        _, constants = self.dummy_price(self.pi_value)
        allowance = mp.mpf(constants['phase_error']['upper'])
        arguments = np.array([-2000, -100, -np.pi, -1, 0, 1, np.pi, 100, 2000], dtype=screen.LD)
        values, maximum, quotient = screen.phase_values(arguments, self.pi_value, self.coefficients)
        self.assertLessEqual(maximum, 3.2)
        self.assertLessEqual(quotient, constants['phase_integer_bound'])
        for argument, value in zip(arguments, values):
            truth = mp.exp(-1j*self.owner.lower(screen.exact_extended(argument)))
            self.assertLessEqual(abs(self.exact_complex(value)-truth), allowance)

    def test_moment_series_both_parities_against_independent_integral(self):
        _, constants = self.dummy_price(self.pi_value)
        relative = mp.mpf(constants['moment_relative_error']['upper'])
        alpha = np.array([-3, -2.82, -1e-9, 0, 1e-9, 2.82, 3], dtype=screen.LD)
        values = screen.moment_values(alpha, self.coefficients)
        for index, argument in enumerate(alpha):
            exact = self.owner.lower(screen.exact_extended(argument))
            for degree in range(7):
                truth = mp.quad(lambda coordinate: coordinate**degree*mp.exp(-1j*exact*coordinate), [-1, 0, 1])
                self.assertLessEqual(abs(self.exact_complex(values[index, degree])-truth), relative*2/(degree+1))
                self.assertEqual(values[index, degree].real if degree % 2 else values[index, degree].imag, 0)

    def test_injected_pi_error_is_charged(self):
        coarse_pi = screen.LD('3.14')
        _, constants = self.dummy_price(coarse_pi)
        values, _, _ = screen.phase_values(np.array([-2000, 2000], dtype=screen.LD), coarse_pi, self.coefficients)
        allowance = mp.mpf(constants['phase_error']['upper'])
        self.assertGreater(allowance, mp.mpf('0.1'))
        for argument, value in zip((-2000, 2000), values):
            self.assertLessEqual(abs(self.exact_complex(value)-mp.exp(-1j*argument)), allowance)

    def test_pairwise_sum_counts_and_rounding_allowance(self):
        for count in (1, 2, 3, 7, 8, 17):
            accumulator = screen.PairwiseAccumulator()
            values = [screen.CD(((-1)**index)*1e20+1j*(index+1)) for index in range(count)]
            for value in values:
                accumulator.add(np.array([value], dtype=screen.CD))
            computed = self.exact_complex(accumulator.finish()[0])
            truth = sum((self.exact_complex(value) for value in values), mp.mpc(0))
            mass = sum(abs(self.exact_complex(value)) for value in values)
            depth = math.ceil(math.log2(count))
            unit = mp.mpf(2)**-64
            allowance = mp.sqrt(2)*depth*unit/(1-depth*unit)*mass
            self.assertEqual(accumulator.count, count)
            self.assertLessEqual(abs(computed-truth), allowance)
        with self.assertRaises(ValueError):
            screen.PairwiseAccumulator().finish()

    def test_chunk_size_does_not_change_execution_order(self):
        families = [(1.6, 0.0), (2.0, 0.25)]
        model, _, _ = screen.prepare(families, np.array([2-3j, -1+2j]), np.array([1+2j, 3-1j]), panels=16)
        xi = np.array([-1, 0, 1])
        first, reading = screen.evaluate(model, xi, self.pi_value, self.coefficients, chunk=1)
        second, _ = screen.evaluate(model, xi, self.pi_value, self.coefficients, chunk=7)
        self.assertTrue(np.array_equal(first, second))
        self.assertEqual(reading['term_count'], 32)
        with self.assertRaises(ValueError):
            screen.evaluate(model, np.array([41]), self.pi_value, self.coefficients)
        with self.assertRaises(ValueError):
            screen.moment_values(np.array([3.01], dtype=screen.LD), self.coefficients)
        with self.assertRaises(ValueError):
            screen.evaluate(model, xi, self.pi_value, self.coefficients, chunk=0)

    def test_uniform_moment_domain_refuses_coarse_panel_model(self):
        model = {'theta': [79.0], 'centers': np.array([-6.55, 6.55], dtype=screen.LD),
                 'radius': screen.LD('0.1'), 'panels': 768}
        totals = {'base': {'mass': mp.iv.mpf(1)}}
        with self.assertRaisesRegex(ValueError, 'full-window moment'):
            screen.arithmetic_price(model, totals, self.pi_value)

    def test_artifact_scope_controls_and_complete_budget(self):
        artifact = json.loads(screen.OUT.read_text(encoding='utf-8'))
        self.assertFalse(artifact['certificate'])
        self.assertFalse(artifact['hgap_closed'])
        self.assertEqual(artifact['owner']['family_count'], 30)
        self.assertEqual(len(artifact['panel_rows']), 768)
        self.assertLess(mp.mpf(artifact['constants']['analytic_alpha_bound']['upper']), 3)
        self.assertLess(mp.mpf(artifact['constants']['analytic_reduced_phase_bound']['upper']), mp.mpf('3.2'))
        self.assertTrue(all(artifact['coefficient_control'].values()))
        self.assertEqual(len(artifact['independent_controls']), 10)
        self.assertTrue(all(row['allowance_ratio'] <= 1 for row in artifact['independent_controls']))
        self.assertEqual({row['xi_step'] for row in artifact['rows']}, {0.02, 0.01, 0.005})
        for row in artifact['rows']:
            self.assertEqual(row['prime_power_count'], 41136)
            self.assertEqual(row['engine']['term_count'], 19200)
            self.assertEqual(row['engine']['pairwise_depth'], 15)
            self.assertLessEqual(row['engine']['max_alpha'], 3)
            self.assertLessEqual(row['engine']['max_reduced_phase'], 3.2)
            self.assertLessEqual(row['engine']['max_phase_integer'], artifact['constants']['phase_integer_bound'])
            self.assertEqual(row['sampled_budget_ratio'], row['reading']['sampled_majorant_charge']/1e7)
        source = json.loads(screen.bridge.refined.OUT.read_text(encoding='utf-8'))
        for channel, charges in artifact['charges'].items():
            for slot in ('coefficient', 'geometry', 'mass'):
                lower = sum((mp.mpf(row[channel][slot]['lower']) for row in artifact['panel_rows']), mp.mpf(0))
                upper = sum((mp.mpf(row[channel][slot]['upper']) for row in artifact['panel_rows']), mp.mpf(0))
                self.assertLessEqual(lower, mp.mpf(charges[slot]['upper']))
                self.assertGreaterEqual(upper, mp.mpf(charges[slot]['lower']))
            expected_lower = mp.mpf(source['refined_reading'][channel+'_radius']['upper'])+sum(
                (mp.mpf(charges[slot]['lower']) for slot in ('coefficient', 'geometry', 'execution', 'pairwise_sum', 'final_cast')), mp.mpf(0))
            expected_upper = mp.mpf(source['refined_reading'][channel+'_radius']['upper'])+sum(
                (mp.mpf(charges[slot]['upper']) for slot in ('coefficient', 'geometry', 'execution', 'pairwise_sum', 'final_cast')), mp.mpf(0))
            self.assertLessEqual(expected_lower, mp.mpf(charges['combined_radius']['upper']))
            self.assertGreaterEqual(expected_upper, mp.mpf(charges['combined_radius']['lower']))

    def test_artifact_provenance(self):
        artifact = json.loads(screen.OUT.read_text(encoding='utf-8'))
        for name, expected in artifact['source_sha256'].items():
            self.assertEqual(hashlib.sha256((screen.ROOT/name).read_bytes()).hexdigest(), expected)


if __name__ == '__main__':
    unittest.main()
