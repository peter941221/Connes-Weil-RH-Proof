"""Independent basis, support, norm and ledger controls for record 2300."""
import hashlib
import json
import unittest
from unittest.mock import patch

import mpmath as mp
import numpy as np

import routea_carrier_coefficient_bridge_price_2300 as screen


class CoefficientBridgeControls(unittest.TestCase):
    def setUp(self):
        mp.mp.dps = 100
        mp.iv.dps = 80

    def assert_contains(self, box, truth):
        owner = screen.refined.remainder.jets.repaired
        self.assertLessEqual(owner.lower(box.real), truth.real)
        self.assertGreaterEqual(owner.upper(box.real), truth.real)
        self.assertLessEqual(owner.lower(box.imag), truth.imag)
        self.assertGreaterEqual(owner.upper(box.imag), truth.imag)

    def test_cosine_clock_against_independent_high_precision(self):
        rational = {0: '1', 2: '0.5', 3: '0', 4: '-0.5', 6: '-1', 8: '-0.5', 9: '0', 10: '0.5'}
        for index in range(-24, 25):
            residue = index % 12
            truth = mp.mpf(rational[residue]) if residue in rational else mp.cos(mp.pi*residue/6)
            self.assert_contains(screen.exact_cosine(index), truth)

    def test_closed_interpolation_matrix_reproduces_every_monomial(self):
        matrix = screen.interpolation_matrix()
        for order in range(7):
            samples = [screen.exact_cosine(node)**order for node in range(7)]
            for degree in range(7):
                coefficient = sum((matrix[degree][node]*samples[node] for node in range(7)), mp.iv.mpf(0))
                self.assert_contains(coefficient, mp.mpc(int(order == degree)))

    def test_envelope_against_independent_formula_both_sides(self):
        for width in (1.6, 1.7600000000000002, 2.5600000000000005):
            radius = mp.mpf(width)**2
            for fraction in ('-1.1', '-1', '-0.99', '-0.5', '0', '0.5', '0.99', '1', '1.1'):
                point = radius*mp.mpf(fraction)
                value = screen.envelope_interval(mp.iv.mpf(point), width)
                truth = mp.exp(-30/(1-(point/radius)**2)+point/2) if abs(point) < radius else mp.mpf(0)
                self.assert_contains(value, mp.mpc(truth))

    def test_coefficient_l1_radius_dominates_independent_integral(self):
        ideal = [mp.iv.mpc(1, 2), mp.iv.mpc(-3, 1), mp.iv.mpc(2, -1)]
        candidate = np.array([1.1+2j, -3+1.2j, 2.2-1.1j])
        radius = mp.iv.mpf('0.3')
        bound = screen.coefficient_radius(ideal, candidate, radius)
        exact = [mp.mpc(1, 2), mp.mpc(-3, 1), mp.mpc(2, -1)]
        difference = lambda value: abs(sum((mp.mpc(float(candidate[degree].real), float(candidate[degree].imag))-coefficient)*value**degree
                                               for degree, coefficient in enumerate(exact)))
        truth = mp.mpf('0.3')*mp.quad(difference, [-1, 0, 1])
        self.assertLessEqual(truth, screen.refined.remainder.jets.repaired.upper(bound))

    def test_regenerated_cast_encloses_both_complex_components(self):
        ideal = [mp.iv.mpc(mp.iv.mpf(1)/3, mp.iv.sqrt(2)), mp.iv.mpc(mp.iv.pi, -mp.iv.sqrt(3))]
        cast = screen.regenerated_coefficients(ideal)
        charge = screen.coefficient_radius(ideal, cast, mp.iv.mpf(1))
        self.assertGreater(screen.refined.remainder.jets.repaired.upper(charge), 0)
        self.assertLess(screen.refined.remainder.jets.repaired.upper(charge), mp.mpf('1e-14'))

    def test_ledger_scope_and_panel_sum(self):
        artifact = json.loads(screen.OUT.read_text(encoding='utf-8'))
        self.assertFalse(artifact['certificate'])
        self.assertFalse(artifact['hgap_closed'])
        reading = artifact['reading']
        self.assertEqual(reading['panels'], 768)
        self.assertEqual([row['panel'] for row in reading['rows']], list(range(768)))
        for channel, totals in reading['totals'].items():
            for slot, total in totals.items():
                lower = sum((mp.mpf(row[channel][slot]['lower']) for row in reading['rows']), mp.mpf(0))
                upper = sum((mp.mpf(row[channel][slot]['upper']) for row in reading['rows']), mp.mpf(0))
                self.assertLessEqual(lower, mp.mpf(total['upper']))
                self.assertGreaterEqual(upper, mp.mpf(total['lower']))
        self.assertEqual(len(artifact['rows']), 6)
        self.assertEqual({row['xi_step'] for row in artifact['rows']}, {0.02, 0.01, 0.005})
        for row in artifact['rows']:
            self.assertAlmostEqual(sum(row['reading']['channel_charges'])/row['reading']['sampled_majorant_charge'], 1, places=12)
            self.assertEqual(row['sampled_budget_ratio'], row['reading']['sampled_majorant_charge']/1e7)

    def test_source_provenance(self):
        artifact = json.loads(screen.OUT.read_text(encoding='utf-8'))
        for name, expected in artifact['source_sha256'].items():
            self.assertEqual(hashlib.sha256((screen.ROOT/name).read_bytes()).hexdigest(), expected)

    def test_mismatched_profile_refused(self):
        source = json.loads(screen.refined.OUT.read_text(encoding='utf-8'))
        source['refined_reading']['panels'] = 384
        with patch.object(screen.Path, 'read_text', return_value=json.dumps(source)):
            with self.assertRaisesRegex(ValueError, '768:6'):
                screen.read_refined_source()


if __name__ == '__main__':
    unittest.main()
