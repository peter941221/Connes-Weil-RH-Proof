"""Independent high-order and stored-ledger controls for record 2297."""
from decimal import Decimal
import hashlib
import json
import unittest

import mpmath as mp

import routea_carrier_envelope_remainder_price_2297 as price
from routea_interval_fifth_derivative_selftest_2292 import reference


class EnvelopeRemainderControls(unittest.TestCase):
    def setUp(self):
        mp.mp.dps = 100
        mp.iv.dps = 70

    def assert_contains(self, box, truth):
        self.assertLessEqual(price.jets.repaired.lower(box.real), truth.real)
        self.assertGreaterEqual(price.jets.repaired.upper(box.real), truth.real)
        self.assertLessEqual(price.jets.repaired.lower(box.imag), truth.imag)
        self.assertGreaterEqual(price.jets.repaired.upper(box.imag), truth.imag)

    def test_seventh_and_eighth_against_independent_diff(self):
        families = [(1.6, 0.0), (2.0, 0.0)]
        coefficients = [2-3j, -1+2j]
        for order in (7, 8):
            for point in (-2, -0.5, 0, 0.5, 2):
                with self.subTest(order=order, point=point):
                    jet, _ = price.jets.grouped_derivative(mp.iv.mpf(point), families, coefficients, order)
                    truth = mp.diff(lambda value: reference(value, families, coefficients), mp.mpf(point), order)
                    self.assert_contains(jet, truth)

    def test_flat_support_edges_both_signs_and_orders(self):
        families = [(1.6, 0.0)]
        radius = mp.mpf(1.6)**2
        for sign in (-1, 1):
            endpoints = sorted((sign*(radius-mp.mpf('0.03')), sign*(radius+mp.mpf('0.01'))))
            for order in (7, 8):
                jet, edges = price.jets.grouped_derivative(mp.iv.mpf(endpoints), families, [2-3j], order)
                self.assertEqual(edges, 1)
                for fraction in ('0.1', '0.5', '0.9'):
                    point = sign*(radius-mp.mpf('0.03')*mp.mpf(fraction))
                    truth = mp.diff(lambda value: reference(value, families, [2-3j]), point, order)
                    self.assert_contains(jet, truth)
                self.assert_contains(jet, mp.mpc(0))

    def test_centered_seventh_bound_contains_interior_samples(self):
        families = [(1.6, 0.0), (2.0, 0.0)]
        coefficients = [2-3j, -1+2j]
        box = mp.iv.mpf(['0.1', '0.2'])
        center = (box.a+box.b)/2
        radius = (box.b-box.a)/2
        seventh, _ = price.jets.grouped_derivative(center, families, coefficients, 7)
        eighth, _ = price.jets.grouped_derivative(box, families, coefficients, 8)
        bound = price.jets.repaired.upper(abs(seventh)+radius*abs(eighth))
        for point in ('0.1', '0.15', '0.2'):
            truth = mp.diff(lambda value: reference(value, families, coefficients), mp.mpf(point), 7)
            self.assertLessEqual(abs(truth), bound)

    def test_carrier_grouping_keeps_every_coefficient(self):
        _, families, base, correction = price.carrier.SOURCE.load_owner()
        groups = price.carrier.carrier_groups(families)
        self.assertEqual(sorted(index for _, indices in groups for index in indices), list(range(30)))
        self.assertEqual(len(groups), 25)
        for coefficients in (base, correction):
            actual = price.channel_coefficients(families, coefficients)
            for (theta, indices), (actual_theta, widths) in zip(groups, actual):
                self.assertEqual(theta, actual_theta)
                for width, box in widths.items():
                    expected = sum((mp.mpc(float(coefficients[index].real), float(coefficients[index].imag))
                                    for index in indices if families[index][0] == width), mp.mpc(0))
                    self.assert_contains(box, expected)

    def test_artifact_scope_hashes_and_panel_sum(self):
        artifact = json.loads(price.OUT.read_text(encoding='utf-8'))
        self.assertFalse(artifact['certificate'])
        self.assertFalse(artifact['hgap_closed'])
        self.assertEqual(artifact['weight_cell']['prime_power_count'], 41136)
        reading = artifact['reading']
        self.assertEqual(len(reading['rows']), reading['panels'])
        self.assertEqual([row['panel'] for row in reading['rows']], list(range(192)))
        for channel in ('base', 'corr'):
            lower = sum((mp.mpf(row[channel+'_panel_radius']['lower']) for row in reading['rows']), mp.mpf(0))
            upper = sum((mp.mpf(row[channel+'_panel_radius']['upper']) for row in reading['rows']), mp.mpf(0))
            total = reading[channel+'_radius']
            self.assertLessEqual(lower, mp.mpf(total['upper']))
            self.assertGreaterEqual(upper, mp.mpf(total['lower']))
        self.assertLess(Decimal(artifact['origin_floor_budget_ratio']['upper']), Decimal(1))
        for path, expected in artifact['source_sha256'].items():
            self.assertEqual(hashlib.sha256((price.ROOT/path).read_bytes()).hexdigest(), expected)


if __name__ == '__main__':
    unittest.main()
