"""Independent algebra and same-owner ledger controls for record 2299."""
import hashlib
import json
import unittest

import mpmath as mp
import numpy as np

import routea_carrier_refined_remainder_screen_2299 as screen


class RefinedRemainderControls(unittest.TestCase):
    def test_integration_keeps_kernel_sign_only_in_signed_channel(self):
        xi = np.array([-1.0, 0.0, 1.0])
        candidate = np.array([[1+2j, 3-1j], [2-1j, 1+1j], [3+1j, 2-3j]])
        kernel = np.array([-2.0, 1.0, -3.0])
        reading = screen.integrate_profile(xi, candidate, kernel, 0.1, 0.2)
        polynomial = np.abs(screen.remainder.carrier.SOURCE.annihilator(xi))**2
        terms = screen.propagation.error_terms(np.abs(candidate[:, 0]), np.abs(candidate[:, 1]), 0.1, 0.2)
        expected = float(np.trapezoid(np.abs(kernel)*polynomial*sum(terms), xi))
        self.assertEqual(reading['sampled_majorant_charge'], expected)
        self.assertAlmostEqual(sum(reading['channel_charges'])/expected, 1, places=14)
        signed = float(np.trapezoid(kernel*polynomial*np.abs(candidate[:, 0])**2*np.abs(candidate[:, 1])**2, xi))
        self.assertEqual(reading['sampled_signed_integral'], signed)

    def test_zero_radii_give_zero_charge(self):
        xi = np.array([-1.0, 0.0, 1.0])
        candidate = np.ones((3, 2), dtype=complex)
        reading = screen.integrate_profile(xi, candidate, np.array([-1.0, 2.0, -3.0]), 0, 0)
        self.assertEqual(reading['sampled_majorant_charge'], 0)
        self.assertEqual(reading['channel_charges'], [0, 0, 0])

    def test_upward_radius_conversion(self):
        reading = {'base_radius': {'upper': '0.1'}, 'corr_radius': {'upper': '0.2'}}
        self.assertGreater(screen.upward_radius(reading, 'base'), 0.1)
        self.assertGreater(screen.upward_radius(reading, 'corr'), 0.2)

    def test_baseline_matches_entire_predecessor_ledger(self):
        artifact = json.loads(screen.OUT.read_text(encoding='utf-8'))
        predecessor = json.loads(screen.remainder.OUT.read_text(encoding='utf-8'))
        self.assertTrue(artifact['baseline_panel_ledger_bitwise'])
        self.assertEqual(artifact['baseline_reading'], predecessor['reading'])

    def test_refined_panel_ledger_sums_and_scope(self):
        mp.mp.dps = 100
        artifact = json.loads(screen.OUT.read_text(encoding='utf-8'))
        self.assertFalse(artifact['certificate'])
        self.assertFalse(artifact['hgap_closed'])
        self.assertEqual(artifact['owner']['family_count'], 30)
        reading = artifact['refined_reading']
        self.assertEqual(reading['degree'], 6)
        self.assertEqual(reading['carrier_count'], 25)
        self.assertEqual(reading['panels'], 768)
        self.assertEqual([row['panel'] for row in reading['rows']], list(range(768)))
        for channel in ('base', 'corr'):
            lower = sum((mp.mpf(row[channel+'_panel_radius']['lower']) for row in reading['rows']), mp.mpf(0))
            upper = sum((mp.mpf(row[channel+'_panel_radius']['upper']) for row in reading['rows']), mp.mpf(0))
            self.assertLessEqual(lower, mp.mpf(reading[channel+'_radius']['upper']))
            self.assertGreaterEqual(upper, mp.mpf(reading[channel+'_radius']['lower']))

    def test_grid_ledger_matches_controls_and_verdict(self):
        artifact = json.loads(screen.OUT.read_text(encoding='utf-8'))
        self.assertEqual({row['xi_step'] for row in artifact['rows']}, {0.02, 0.01, 0.005})
        for row in artifact['rows']:
            self.assertEqual(row['prime_power_count'], 41136)
            self.assertLessEqual(row['baseline_relative_movement'], 1e-12)
            self.assertEqual(row['refined_budget_ratio'], row['refined']['sampled_majorant_charge']/1e7)
            self.assertGreaterEqual(row['candidate_difference_absolute'],
                                    abs(row['candidate_difference_signed'])*0.9999999999)
            self.assertAlmostEqual(sum(row['refined']['channel_charges'])/row['refined']['sampled_majorant_charge'], 1, places=12)
        self.assertEqual(artifact['sampled_majorant_pass_all_grids'],
                         all(row['refined_budget_ratio'] <= 1 for row in artifact['rows']))

    def test_source_provenance(self):
        artifact = json.loads(screen.OUT.read_text(encoding='utf-8'))
        for name, expected in artifact['source_sha256'].items():
            self.assertEqual(hashlib.sha256((screen.ROOT/name).read_bytes()).hexdigest(), expected)


if __name__ == '__main__':
    unittest.main()
