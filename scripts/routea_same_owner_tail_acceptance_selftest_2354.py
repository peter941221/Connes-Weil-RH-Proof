"""2354: parameterized exact acceptance and owner/provenance controls."""
from fractions import Fraction
import hashlib
import json
import tempfile
from pathlib import Path
import unittest

import routea_same_owner_tail_acceptance_2354 as acceptance


class TailAcceptanceTests(unittest.TestCase):
    def test_dyadic_upper_contains_bound_and_next_does_not(self):
        for upper in (Fraction(1, 2), Fraction(3, 8), Fraction(1, 10), Fraction(1, 100)):
            exponent, bound = acceptance.get_dyadic_contraction(upper)
            self.assertGreaterEqual(bound, upper)
            self.assertLess(bound / 2, upper)
            self.assertEqual(bound, Fraction(1, 2**exponent))

    def test_invalid_contraction_upper_rejected(self):
        for upper in (0, -1, 1, 2):
            with self.assertRaises(ValueError):
                acceptance.get_dyadic_contraction(upper)

    def test_registered_q52_is_from_same_supplier(self):
        supplier = json.loads(acceptance.SUPPLIER.read_text())
        exponent, bound = acceptance.get_dyadic_contraction(supplier["contour_base_upper_T128_exact"])
        self.assertEqual(exponent, 52)
        self.assertEqual(bound, Fraction(1, 2**52))

    def test_n2_lane_passes_with_strict_reserve(self):
        ratio = acceptance.get_acceptance_ratio(Fraction(1, 2**52), 2, 6, 256)
        self.assertLess(ratio, 1)
        self.assertGreater(ratio, Fraction(3, 4))

    def test_n3_small_coefficient_lane_passes(self):
        ratio = acceptance.get_acceptance_ratio(Fraction(1, 2**52), 3, 6, Fraction(1, 10**13))
        self.assertLess(ratio, Fraction(1, 4))
        self.assertGreater(ratio, Fraction(1, 5))

    def test_smaller_lambda_can_fail_on_same_iterate(self):
        self.assertGreater(acceptance.get_acceptance_ratio(Fraction(1, 2**52), 2, 6, 1), 1)
        self.assertGreater(acceptance.get_acceptance_ratio(Fraction(1, 2**52), 3, 6, Fraction(1, 10**14)), 1)

    def test_legacy_q14_needs_later_iterate_at_lambda_one(self):
        self.assertGreater(acceptance.get_acceptance_ratio(Fraction(1, 2**14), 7, 6, 1), 1)
        self.assertLess(acceptance.get_acceptance_ratio(Fraction(1, 2**14), 8, 6, 1), 1)

    def test_ratio_decreases_with_positive_lambda(self):
        for iterate in (0, 2, 3):
            values = [acceptance.get_acceptance_ratio(Fraction(1, 2**52), iterate, 6, coefficient)
                      for coefficient in (Fraction(1, 10**13), Fraction(1), Fraction(256), Fraction(10**9))]
            self.assertEqual(values, sorted(values, reverse=True))

    def test_lambda_stays_in_both_budget_and_prefix(self):
        orbit = (3 + acceptance.RHO_NORM_CAP)**4
        for coefficient in (Fraction(1, 10**13), Fraction(1), Fraction(256)):
            direct = (acceptance.RESERVE * 4 * acceptance.MULTIPLICITY_CAP * Fraction(3, 4)**6 * orbit *
                      (orbit + coefficient)**2 * (Fraction(1, 2**52)**2 * acceptance.D4_CAP * acceptance.D2_CAP)**2 /
                      coefficient**2)
            self.assertEqual(direct, acceptance.get_acceptance_ratio(Fraction(1, 2**52), 2, 6, coefficient))

    def test_reserve_multiplies_the_acceptance_charge(self):
        first = acceptance.get_acceptance_ratio(Fraction(1, 2**52), 2, 6, 256, reserve=Fraction(3, 2))
        second = acceptance.get_acceptance_ratio(Fraction(1, 2**52), 2, 6, 256, reserve=Fraction(2))
        self.assertEqual(second / first, Fraction(4, 3))

    def test_iteration_ratio_has_two_power_factors(self):
        first = acceptance.get_acceptance_ratio(Fraction(1, 2**52), 2, 6, 256)
        second = acceptance.get_acceptance_ratio(Fraction(1, 2**52), 3, 6, 256)
        self.assertEqual(second / first, Fraction(1, 2**104))

    def test_shell_ratio_has_exact_geometric_factor(self):
        first = acceptance.get_acceptance_ratio(Fraction(1, 2**52), 2, 6, 256)
        second = acceptance.get_acceptance_ratio(Fraction(1, 2**52), 2, 7, 256)
        self.assertEqual(second / first, Fraction(3, 4))

    def test_mass_scales_inverse_ratio(self):
        first = acceptance.get_acceptance_ratio(Fraction(1, 2**52), 2, 6, 256)
        second = acceptance.get_acceptance_ratio(Fraction(1, 2**52), 2, 6, 256, mass=2)
        self.assertEqual(second, first / 2)

    def test_invalid_acceptance_inputs_rejected(self):
        variants = [{"q": 0}, {"q": 1}, {"iterate": -1}, {"iterate": Fraction(1, 2)},
                    {"shell": -1}, {"coefficient": 0}, {"coefficient": -1},
                    {"rho_norm": -1}, {"d4": 0}, {"d2": 0}, {"mass": 0}, {"reserve": 1}]
        for variant in variants:
            params = {"q": Fraction(1, 2**52), "iterate": 2, "shell": 6, "coefficient": 256}
            params.update(variant)
            with self.subTest(variant=variant), self.assertRaises(ValueError):
                acceptance.get_acceptance_ratio(**params)

    def test_provenance_mutation_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "owner").write_bytes(b"original owner")
            payload = {"source_sha256": {"owner": hashlib.sha256(b"original owner").hexdigest()}, "input_sha256": {}}
            acceptance.verify_hashes(payload, root)
            (root / "owner").write_bytes(b"changed owner")
            with self.assertRaises(ValueError):
                acceptance.verify_hashes(payload, root)

    def test_supplier_hashes_match_current_bytes(self):
        acceptance.verify_hashes(json.loads(acceptance.SUPPLIER.read_text()))

    def test_support_composition_matches_the_actual_iterate(self):
        for iterate in (0, 2, 3, 8):
            cover = acceptance.premise.get_support_cover([Fraction(2), Fraction(3)], iterate)
            self.assertEqual(Fraction(cover["source_radius_cover_exact"]), (iterate + 2) * 3)
            self.assertEqual(Fraction(cover["square_radius_cover_exact"]), 2 * (iterate + 2) * 3)
            self.assertFalse(cover["complete_covering_prime_book_enumerated"])

    def test_lane_is_not_gate_or_actual_acceptance(self):
        row = acceptance.get_ratio_row(Fraction(1, 2**52), 2, 6, Fraction(256))
        self.assertTrue(row["registered_scalar_budget_pass"])
        self.assertTrue(row["not_a_gate_row"])
        self.assertFalse(row["actual_tail_acceptance_instantiated"])


if __name__ == "__main__":
    unittest.main(verbosity=2)
