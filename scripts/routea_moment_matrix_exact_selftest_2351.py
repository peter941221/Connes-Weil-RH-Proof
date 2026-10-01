"""2351: adversarial exact-arithmetic and captured-owner controls."""
import copy
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import unittest

import routea_moment_matrix_exact_check_2351 as check

ROOT = Path(__file__).resolve().parents[1]


def box(real_lower, real_upper, imag_lower=0, imag_upper=0):
    return ((Fraction(real_lower), Fraction(real_upper)),
            (Fraction(imag_lower), Fraction(imag_upper)))


class ExactMomentTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.payload = json.loads((ROOT / "results/2351_moment_matrix_witness.json").read_text())
        cls.result = json.loads((ROOT / "results/2351_moment_matrix_exact_check.json").read_text())

    def test_hexadecimal_capture_is_decoded_without_float(self):
        self.assertEqual(check.hex_fraction("0x1.c28f5c28f5c29p+0"), Fraction(7926335344172073, 4503599627370496))
        self.assertEqual(check.hex_fraction("-0x1.8000000000000p-2"), Fraction(-3, 8))
        self.assertEqual(check.hex_fraction("0x0.0000000000001p-1022"), Fraction(1, 2**1074))
        for text in ("nan", "inf", "1.0", "0x1p+0"):
            with self.assertRaises(ValueError):
                check.hex_fraction(text)

    def test_complex_multiplication_and_full_component_magnitude(self):
        self.assertEqual(check.complex_mul(check.point(3, 4), check.point(-2, 1)), check.point(-10, -5))
        self.assertEqual(check.l1_upper(check.point(3, 4)), 7)
        self.assertGreaterEqual(check.l1_upper(check.point(3, 4))**2, 3**2 + 4**2)

    def test_interval_multiplication_includes_all_endpoint_products(self):
        left, right = (Fraction(-2), Fraction(3)), (Fraction(-5), Fraction(7))
        enclosed = check.real_mul(left, right)
        self.assertEqual(enclosed, (Fraction(-15), Fraction(21)))
        for first in left:
            for second in right:
                self.assertLessEqual(enclosed[0], first * second)
                self.assertLessEqual(first * second, enclosed[1])

    def test_small_exact_system_passes(self):
        result = check.verify([[check.point(2)]], [[check.point(Fraction(1, 2))]],
                              [[check.point(3)]], [[box("1.4", "1.6", "-0.1", "0.1")]])
        self.assertEqual(Fraction(result["eta_exact"]), 0)
        self.assertTrue(result["coefficient_boxes_invariant"])

    def test_uncertain_entry_system_passes_without_rounding(self):
        result = check.verify([[box("1.999", "2.001")]], [[check.point(Fraction(1, 2))]],
                              [[check.point(3)]], [[box("1.4", "1.6", "-0.1", "0.1")]])
        self.assertEqual(Fraction(result["eta_exact"]), Fraction(1, 2000))
        self.assertTrue(result["coefficient_boxes_invariant"])

    def test_singular_and_wrong_inverse_are_rejected(self):
        for matrix, inverse in ((check.point(0), check.point(1)), (check.point(2), check.point(-1))):
            with self.assertRaises(ValueError):
                check.verify([[matrix]], [[inverse]], [[check.point(3)]], [[box(1, 2)]])

    def test_correct_inverse_does_not_certify_wrong_coefficient_box(self):
        result = check.verify([[check.point(2)]], [[check.point(Fraction(1, 2))]],
                              [[check.point(3)]], [[box("1.9", "2.1")]])
        self.assertTrue(result["neumann_pass"])
        self.assertFalse(result["coefficient_boxes_invariant"])

    def test_degenerate_boxes_have_explicit_containment(self):
        for center, expected in ((Fraction(3, 2), True), (Fraction(2), False)):
            result = check.verify([[check.point(2)]], [[check.point(Fraction(1, 2))]],
                                  [[check.point(3)]], [[check.point(center)]])
            self.assertEqual(result["coefficient_boxes_invariant"], expected)
        self.assertIsNone(result["channels"][0]["components"][0]["ratio_exact"])

    def test_inverted_exported_interval_is_rejected(self):
        with self.assertRaises(ValueError):
            check.real_interval({"lower_exact": "2", "upper_exact": "1"})

    def test_dimensions_and_nonpoint_inverse_are_rejected(self):
        with self.assertRaises(ValueError):
            check.verify([], [], [], [])
        with self.assertRaises(ValueError):
            check.verify([[check.point(2), check.point(0)]], [[check.point(1)]],
                         [[check.point(3)]], [[box(1, 2)]])
        with self.assertRaises(ValueError):
            check.verify([[check.point(2)]], [[box("0.4", "0.6")]],
                         [[check.point(3)]], [[box(1, 2)]])
        with self.assertRaises(ValueError):
            check.verify([[check.point(2)]], [[check.point(Fraction(1, 2))]],
                         [[check.point(3), check.point(0)]], [[box(1, 2)]])

    def test_actual_owner_replay_is_identical(self):
        self.assertEqual(check.run(ROOT / "results/2351_moment_matrix_witness.json"), self.result)

    def test_all_original_coefficient_components_are_contained(self):
        self.assertLess(Fraction(self.result["eta_exact"]), Fraction(1, 2))
        self.assertTrue(self.result["coefficient_boxes_invariant"])
        self.assertEqual(len(self.result["channels"]), 2)
        for channel in self.result["channels"]:
            self.assertEqual(len(channel["components"]), 60)
            self.assertLess(Fraction(channel["maximum_finite_ratio_exact"]), 1)
            for component in channel["components"]:
                self.assertTrue(component["contained"])
                self.assertGreaterEqual(Fraction(component["lower_margin_exact"]), 0)
                self.assertGreaterEqual(Fraction(component["upper_margin_exact"]), 0)

    def test_parent_and_checker_hashes_match(self):
        self.assertEqual(self.result["source_sha256"], hashlib.sha256(Path(check.__file__).read_bytes()).hexdigest())
        self.assertEqual(self.result["witness_sha256"], hashlib.sha256(
            (ROOT / "results/2351_moment_matrix_witness.json").read_bytes()).hexdigest())
        check.validate_owner(self.payload)

    def test_rejects_changed_matrix_even_with_same_owner_labels(self):
        changed = copy.deepcopy(self.payload)
        changed["matrix"][0][0]["real"]["upper_exact"] = "1"
        with self.assertRaises(ValueError):
            check.validate_owner(changed)

    def test_rejects_widened_coefficient_rectangles(self):
        changed = copy.deepcopy(self.payload)
        changed["coefficient_rectangles"][0][0]["real"]["upper_exact"] = "999999999999999999999999"
        with self.assertRaises(ValueError):
            check.validate_owner(changed)

    def test_rejects_changed_nodes_targets_radii_and_modulations(self):
        for field in ("nodes", "right_hand_sides", "support_radii_exact", "modulations_exact"):
            changed = copy.deepcopy(self.payload)
            if field == "nodes":
                changed[field][0]["imag"]["upper_exact"] = "1"
            elif field == "right_hand_sides":
                changed[field][1][0]["real"]["upper_exact"] = "123"
            else:
                changed[field][0] = "0"
            with self.assertRaises(ValueError):
                check.validate_owner(changed)

    def test_scope_flags_remain_external(self):
        for artifact in (self.payload, self.result):
            for flag in ("analytic_matrix_enclosures_imported_in_lean",
                         "coefficient_realization_imported_in_lean",
                         "healthy_detector_instantiated", "producer_go", "rh_claim"):
                self.assertFalse(artifact[flag])


if __name__ == "__main__":
    unittest.main(verbosity=2)

