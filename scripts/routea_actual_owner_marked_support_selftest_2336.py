"""Negative controls for the 2336 owner identity and support diagnostic."""
import unittest

from routea_actual_owner_marked_support_probe_2336 import (
    get_companion_indices,
    get_square_values,
    get_support_geometry,
)


class ActualOwnerProbeTests(unittest.TestCase):
    def test_uneven_companion_pair_preserves_negative_sign(self):
        nodes = [0.7 + 3j, 0.3 + 3j, 0.7 - 3j, 0.3 - 3j]
        indices = get_companion_indices(nodes)
        self.assertEqual(indices, [1, 0, 3, 2])
        self.assertEqual(get_square_values([1, -1, 0j, 0j], indices), [-1, -1, 0j, 0j])

    def test_modulus_square_substitution_would_change_marked_sign(self):
        values = [1 + 0j, -1 + 0j]
        paired = get_square_values(values, [1, 0])
        self.assertEqual(paired, [-1, -1])
        self.assertNotEqual(paired, [abs(value) ** 2 for value in values])

    def test_missing_companion_is_rejected(self):
        with self.assertRaises(ValueError):
            get_companion_indices([0.7 + 3j])

    def test_ambiguous_companion_is_rejected(self):
        with self.assertRaises(ValueError):
            get_companion_indices([0.7 + 3j, 0.3 + 3j, 0.3 + 3j])

    def test_pair_length_mismatch_is_rejected(self):
        with self.assertRaises(ValueError):
            get_square_values([1, -1], [1])

    def test_support_counts_base_and_correction_before_square(self):
        geometry = get_support_geometry([(2.0, 0.0)], 0)
        self.assertEqual(geometry["factor_radius_exact"], "4")
        self.assertEqual(geometry["source_radius_upper_exact"], "8")
        self.assertEqual(geometry["square_radius_upper_exact"], "16")
        self.assertEqual(geometry["single_factor_square_radius_exact"], "8")

    def test_iterate_index_counts_n_plus_one_base_copies(self):
        geometry = get_support_geometry([(2.0, 0.0)], 2)
        self.assertEqual(geometry["base_copy_count"], 3)
        self.assertEqual(geometry["source_radius_upper_exact"], "16")
        self.assertEqual(geometry["square_radius_upper_exact"], "32")

    def test_negative_iterate_index_is_rejected(self):
        with self.assertRaises(ValueError):
            get_support_geometry([(2.0, 0.0)], -1)


if __name__ == "__main__":
    unittest.main()
