"""Algebraic, provenance and sampled-ledger controls for record 2298."""
import hashlib
import json
import unittest

import numpy as np

import routea_carrier_full_window_propagation_screen_2298 as screen


class FullWindowPropagationControls(unittest.TestCase):
    def test_majorant_contains_complex_perturbations(self):
        base = 2+3j
        correction = -1+2j
        for base_radius, corr_radius in ((0, 0), (0.1, 0), (0, 0.2), (0.1, 0.2), (10, 20)):
            charge = sum(screen.error_terms(abs(base), abs(correction), base_radius, corr_radius))
            for base_phase in np.linspace(-np.pi, np.pi, 13):
                for corr_phase in np.linspace(-np.pi, np.pi, 13):
                    perturbed = abs(base+base_radius*np.exp(1j*base_phase))**2 * abs(
                        correction+corr_radius*np.exp(1j*corr_phase))**2
                    difference = abs(perturbed-abs(base)**2*abs(correction)**2)
                    self.assertLessEqual(difference, charge+1e-10*max(1, charge))

    def test_zero_amplitude_retains_quartic_floor(self):
        self.assertEqual(screen.error_terms(0, 0, 2, 3), (0, 0, 36))

    def test_majorant_increases_with_radii(self):
        previous = 0
        for radius in (0, 0.01, 0.1, 1, 10):
            total = sum(screen.error_terms(2, 3, radius, 2*radius))
            self.assertGreaterEqual(total, previous)
            previous = total

    def test_negative_inputs_refused(self):
        for arguments in ((-1, 2, 3, 4), (1, -2, 3, 4), (1, 2, -3, 4), (1, 2, 3, -4)):
            with self.assertRaises(ValueError):
                screen.error_terms(*arguments)
        for step in (0, -1, np.nan, np.inf, 0.03):
            with self.assertRaises(ValueError):
                screen.run(step, 1, 1)

    def test_radii_round_up_and_match_artifact(self):
        base, correction = screen.read_radii()
        artifact = json.loads(screen.remainder.OUT.read_text(encoding='utf-8'))
        self.assertGreater(base, float(artifact['reading']['base_radius']['upper']))
        self.assertGreater(correction, float(artifact['reading']['corr_radius']['upper']))

    def test_ledger_and_provenance(self):
        artifact = json.loads(screen.OUT.read_text(encoding='utf-8'))
        self.assertFalse(artifact['certificate'])
        self.assertFalse(artifact['hgap_closed'])
        self.assertEqual(artifact['window'], [-40, 40])
        self.assertEqual({row['xi_step'] for row in artifact['rows']}, {0.02, 0.01, 0.005})
        for row in artifact['rows']:
            self.assertEqual(row['prime_power_count'], 41136)
            self.assertLessEqual(row['same_candidate_relative_movement'], 1e-12)
            terms = [row[name] for name in ('base_squared_corr_error_charge',
                                            'corr_squared_base_error_charge', 'cross_error_charge')]
            self.assertTrue(all(np.isfinite(term) and term >= 0 for term in terms))
            self.assertAlmostEqual(sum(terms)/row['sampled_majorant_charge'], 1, places=12)
            self.assertEqual(row['sampled_budget_ratio'], row['sampled_majorant_charge']/1e7)
        self.assertEqual(artifact['sampled_majorant_pass_all_grids'],
                         all(row['sampled_budget_ratio'] <= 1 for row in artifact['rows']))
        for name, expected in artifact['source_sha256'].items():
            self.assertEqual(hashlib.sha256((screen.ROOT/name).read_bytes()).hexdigest(), expected)


if __name__ == '__main__':
    unittest.main()
