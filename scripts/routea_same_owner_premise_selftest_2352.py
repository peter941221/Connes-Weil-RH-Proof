"""2352: exact cutoff, owner and scope regression tests."""
import copy
from fractions import Fraction
import json
import unittest

import routea_same_owner_premise_audit_2352 as audit


class SameOwnerPremiseTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.payload = json.loads(audit.WITNESS.read_text())
        cls.nodes = [audit.decode_point(value) for value in cls.payload["nodes"]]
        cls.base, cls.correction = [[audit.decode_point(value) for value in row]
                                  for row in cls.payload["right_hand_sides"]]
        cls.result = audit.run()

    def test_actual_replay_matches_artifact(self):
        stored = json.loads((audit.ROOT / "results/2352_same_owner_premise_audit.json").read_text())
        self.assertEqual(self.result, stored)

    def test_actual_cutoff_floor_is_exact_captured_maximum(self):
        floor = self.result["contraction_floor"]
        self.assertEqual(floor["attaining_node_indices"], [29])
        self.assertEqual(Fraction(floor["threshold_strictly_greater_than_exact"]), abs(self.nodes[29][1]))
        self.assertEqual(floor["minimum_height_shell_index_for_threshold_le_two_pow_succ"], 6)
        self.assertEqual(floor["shell_ceiling_exact"], "128")

    def test_old_cutoff_and_boundary_are_excluded_but_128_is_not_certified(self):
        readings = self.result["cutoff_controls"]
        self.assertEqual([row["excluded_conditional_on_exact_base_realization"] for row in readings],
                         [True, True, True, False])
        self.assertFalse(self.result["uniform_tail_at_T128_certified"])

    def test_mandatory_only_floor_does_not_improve_consumer_height_shell(self):
        floor = self.result["mandatory_target_only_contraction_floor"]
        self.assertEqual(Fraction(floor["threshold_strictly_greater_than_exact"]), abs(self.nodes[0][1]))
        self.assertEqual(floor["minimum_height_shell_index_for_threshold_le_two_pow_succ"], 5)
        for key in ("height_shell_floor_all_nodes", "height_shell_floor_mandatory_targets_only"):
            self.assertEqual(self.result[key]["minimum_shell_index"], 6)
            self.assertEqual(self.result[key]["ceiling_exact"], "128")
        self.assertFalse(self.result["removing_extra_base_constraints_improves_first_healthy_height_shell"])

    def test_height_shell_respects_strict_cutoff_and_inclusive_rho_height(self):
        self.assertEqual(audit.get_height_shell_floor(4, 0)["minimum_shell_index"], 2)
        self.assertEqual(audit.get_height_shell_floor(3, 2)["minimum_shell_index"], 1)

    def test_slab_guard_excludes_large_height_outside_slab(self):
        nodes = [(Fraction(1, 2), Fraction(3)), (Fraction(3, 2), Fraction(1000))]
        targets = [(Fraction(1), Fraction(0))] * 2
        floor = audit.get_contraction_floor(nodes, targets)
        self.assertEqual(floor["threshold_strictly_greater_than_exact"], "3")
        self.assertFalse(audit.get_contraction_obstruction(nodes, targets, 4, Fraction(1, 2))[
            "excluded_conditional_on_exact_base_realization"])

    def test_negative_height_and_inclusive_threshold(self):
        nodes = [(Fraction(0), Fraction(-7))]
        targets = [(Fraction(1), Fraction(0))]
        self.assertTrue(audit.get_contraction_obstruction(nodes, targets, 7, Fraction(999, 1000))[
            "excluded_conditional_on_exact_base_realization"])
        self.assertFalse(audit.get_contraction_obstruction(nodes, targets, Fraction(701, 100), Fraction(1, 2))[
            "excluded_conditional_on_exact_base_realization"])

    def test_unit_bound_does_not_produce_false_obstruction(self):
        reading = audit.get_contraction_obstruction(self.nodes, self.base, 0, 1)
        self.assertFalse(reading["excluded_conditional_on_exact_base_realization"])

    def test_nonunit_targets_do_not_force_unit_floor(self):
        with self.assertRaises(ValueError):
            audit.get_contraction_floor([(Fraction(1, 2), Fraction(20))], [(Fraction(0), Fraction(0))])
        with self.assertRaises(ValueError):
            audit.get_contraction_floor(self.nodes, self.base[:-1])

    def test_mandatory_coordinates_and_targets(self):
        mandatory = audit.validate_mandatory_targets(self.nodes, self.correction)
        self.assertEqual(mandatory["marked_orbit_sum_exact"], "-2")
        changed = list(self.nodes)
        changed[4] = (changed[4][0] + Fraction(1, 1000), changed[4][1])
        with self.assertRaises(ValueError):
            audit.validate_mandatory_targets(changed, self.correction)
        changed_targets = list(self.correction)
        changed_targets[5] = (Fraction(1, 10**30), Fraction(0))
        with self.assertRaises(ValueError):
            audit.validate_mandatory_targets(self.nodes, changed_targets)

    def test_approximate_node_is_not_an_exact_point(self):
        value = copy.deepcopy(self.payload["nodes"][0])
        value["real"]["upper_exact"] = str(Fraction(value["real"]["upper_exact"]) + Fraction(1, 10**40))
        with self.assertRaises(ValueError):
            audit.decode_point(value)

    def test_support_is_composed_at_same_iterate(self):
        covers = self.result["support_covers"]
        radius = Fraction(covers[0]["factor_radius_exact"])
        for iterate, row in enumerate(covers):
            self.assertEqual(Fraction(row["source_radius_cover_exact"]), (iterate + 2) * radius)
            self.assertEqual(Fraction(row["square_radius_cover_exact"]), 2 * (iterate + 2) * radius)
        self.assertNotEqual(covers[0]["square_radius_cover_exact"], covers[0]["single_factor_square_radius_exact"])

    def test_invalid_support_inputs_are_rejected(self):
        for radii, iterate in (([], 0), ([Fraction(0)], 0), ([Fraction(1)], -1), ([Fraction(1)], True)):
            with self.assertRaises(ValueError):
                audit.get_support_cover(radii, iterate)

    def test_scope_flags_preserve_all_open_bridges(self):
        for flag in ("legacy_T28_q_bound_transferred", "uniform_tail_at_T128_certified",
                     "actual_numeric_invertibility_instantiated_in_lean", "healthy_detector_instantiated",
                     "complete_signed_kernel_priced", "map103_reopened", "global_tail_impossibility_claim",
                     "producer_go", "rh_claim"):
            self.assertFalse(self.result[flag])
        self.assertTrue(self.result["removing_extra_constraints_changes_owner"])
        self.assertFalse(self.result["all_node_base_interpolation_required_by_healthy_target_api"])


if __name__ == "__main__":
    unittest.main(verbosity=2)
