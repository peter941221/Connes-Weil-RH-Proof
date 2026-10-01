"""2353: exact tail envelope, normalization and finite-control scope tests."""
from fractions import Fraction
import hashlib
import json
import unittest

from flint import acb, arb, ctx

import routea_same_owner_tail_supplier_2353 as tail


class SameOwnerTailTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.result = json.loads((tail.ROOT / "results/2353_same_owner_tail_supplier.json").read_text())

    def setUp(self):
        ctx.prec = 256
        self.budgets = [{"0": Fraction(10), "2": Fraction(4), "4": Fraction(16)}]

    def test_registered_sources_and_inputs_match(self):
        for key in ("source_sha256", "input_sha256"):
            for relative, digest in self.result[key].items():
                self.assertEqual(hashlib.sha256((tail.ROOT / relative).read_bytes()).hexdigest(), digest)

    def test_shifted_family_bound_uses_safe_absolute_gap(self):
        self.assertEqual(tail.get_tail_upper(self.budgets, [Fraction(3)], 5), 1)
        self.assertEqual(tail.get_tail_upper(self.budgets, [Fraction(-3)], 5), 1)
        self.assertEqual(tail.get_tail_upper(self.budgets, [Fraction(3)], 3), 10)
        self.assertEqual(tail.get_tail_upper(self.budgets, [Fraction(3)], 1), 10)

    def test_both_height_signs_are_dominated_at_and_beyond_threshold(self):
        upper = tail.get_tail_upper(self.budgets, [Fraction(3)], 5)
        for height in (5, -5, 6, -6, 100, -100):
            delta = abs(Fraction(height) + 3)
            point_upper = min(Fraction(10), Fraction(4) / delta**2, Fraction(16) / delta**4)
            self.assertLessEqual(point_upper, upper)

    def test_minimum_of_three_bounds_is_retained(self):
        self.assertEqual(tail.get_tail_upper(self.budgets, [Fraction(0)], 1), 4)
        self.assertEqual(tail.get_tail_upper(self.budgets, [Fraction(0)], 10), Fraction(1, 625))

    def test_envelope_is_monotone_and_ladder_accepts_only_exact_bound(self):
        values = [tail.get_tail_upper(self.budgets, [Fraction(3)], threshold)
                  for threshold in (0, 3, 4, 5, 10)]
        self.assertEqual(values, sorted(values, reverse=True))
        rows = tail.get_threshold_ladder(self.budgets, [Fraction(3)], start=4)
        self.assertFalse(rows[0]["fits_bound"])
        self.assertTrue(rows[-1]["fits_bound"])
        with self.assertRaises(RuntimeError):
            tail.get_threshold_ladder(self.budgets, [Fraction(3)], start=4, steps=1)

    def test_whole_line_constants_cover_low_and_high_frequency_branches(self):
        self.assertEqual(tail.get_whole_line_constant(self.budgets, [Fraction(3)], 2), 360)
        self.assertEqual(tail.get_whole_line_constant(self.budgets, [Fraction(3)], 4), 12960)
        for order in (2, 4):
            constant = tail.get_whole_line_constant(self.budgets, [Fraction(3)], order)
            for height in (0, 1, -3, 5, -6, 6, 100, -100):
                delta = abs(Fraction(height) + 3)
                point_upper = Fraction(10) if delta == 0 else min(
                    Fraction(10), self.budgets[0][str(order)] / delta**order)
                self.assertLessEqual(abs(height)**order * point_upper, constant)

    def test_actual_ladder_and_angular_constants_reconstruct_exactly(self):
        capture = json.loads((tail.ROOT / "results/2275_gap_owner_audit.json").read_text())["owner_capture"]
        modulations = [tail.premise.moment.hex_fraction(pair[1]) for pair in capture["families_hex"]]
        channels = [[{order: Fraction(value) for order, value in channel[str(index)].items()}
                     for index in range(30)] for channel in self.result["family_budgets_exact"]]
        for row in self.result["base_contraction_threshold_ladder"]:
            upper = tail.get_tail_upper(channels[0], modulations, Fraction(row["threshold_exact"]))
            self.assertEqual(upper, Fraction(row["upper_exact"]))
            self.assertEqual(upper <= tail.BOUND, row["fits_bound"])
        constants = self.result["whole_line_angular_constants_exact"]
        self.assertEqual(tail.get_whole_line_constant(channels[0], modulations, 4),
                         Fraction(constants["base_order4"]))
        self.assertEqual(tail.get_whole_line_constant(channels[1], modulations, 2),
                         Fraction(constants["correction_order2"]))

    def test_two_pi_powers_cancel_without_a_numeric_pi_pin(self):
        scale, fourth, second = Fraction(7, 3), Fraction(11, 5), Fraction(13, 2)
        normalized = (2 * scale)**12 * (fourth / (2 * scale)**4 * second / (2 * scale)**2)**2
        self.assertEqual(normalized, (fourth * second)**2)

    def test_finite_point_pass_is_not_a_uniform_certificate(self):
        self.assertEqual(tail.classify_point({"lower_exact": "0", "upper_exact": "1/4"}),
                         "POINT_ONLY_BELOW_BOUND")
        self.assertEqual(tail.classify_point({"lower_exact": "3/4", "upper_exact": "1"}),
                         "POINT_REFUTES_REGISTERED_UNIFORM_BOUND")
        self.assertEqual(tail.classify_point({"lower_exact": "1/4", "upper_exact": "3/4"}),
                         "POINT_UNRESOLVED")
        with self.assertRaises(ValueError):
            tail.classify_point({"lower_exact": "1", "upper_exact": "0"})

    def test_actual_finite_point_verdicts_use_exported_modulus_bounds(self):
        for row in self.result["point_controls_T128"]:
            self.assertEqual(row["base_verdict"], tail.classify_point(row["moduli"][0]))
            self.assertIn(Fraction(row["sigma_exact"]), (0, Fraction(1, 2), 1))
            self.assertIn(Fraction(row["height_exact"]), (128, -128))
            for edge in row["weighted_edge_charges"]:
                self.assertGreater(Fraction(edge["lower_exact"]), 0)

    def test_contour_totals_keep_both_connectors_and_the_real_edges(self):
        geometry = self.result["contour_geometry"]
        self.assertEqual(Fraction(geometry["cut_exact"]), 1 - Fraction(geometry["edge_delta_exact"]))
        self.assertEqual(Fraction(geometry["edge_delta_exact"]), Fraction(1, 8))
        self.assertEqual(self.result["direct_integrator_edge_delta_exact"], "1/64")
        for channels in (self.result["contour_family_bounds_T128"],
                         self.result["baseline_contour_family_bounds_T128"]):
            for channel in channels:
                for row in channel:
                    terms = [Fraction(row[key]) for key in
                             ("top_upper_exact", "connector_upper_exact", "edge_upper_exact")]
                    self.assertTrue(all(value > 0 for value in terms))
                    self.assertEqual(sum(terms), Fraction(row["total_upper_exact"]))
                    self.assertGreater(Fraction(row["carrier_gap_exact"]), 0)

    def test_contour_minimum_and_registered_strong_bound_are_exact(self):
        upper = sum(min(Fraction(row["total_upper_exact"]), Fraction(old["total_upper_exact"]))
                    for row, old in zip(self.result["contour_family_bounds_T128"][0],
                                        self.result["baseline_contour_family_bounds_T128"][0]))
        self.assertEqual(upper, Fraction(self.result["contour_base_upper_T128_exact"]))
        self.assertEqual(upper <= tail.STRONG_BOUND, self.result["T128_q_2neg14_proved"])
        self.assertLessEqual(upper, Fraction(self.result["certified_base_q_exact"]))
        self.assertEqual(self.result["certified_base_threshold_exact"], "128")

    def test_contour_bound_dominates_an_actual_binding_family_in_both_signs(self):
        families, _, _, coefficients, _ = tail.direct.load_ideal_source()
        width, modulation = families[29]
        bound = min(Fraction(self.result[key][0][29]["total_upper_exact"])
                    for key in ("contour_family_bounds_T128", "baseline_contour_family_bounds_T128"))
        for height in (128, -128):
            value, _ = tail.certificate.integrate_family(width, modulation, acb(1, height), panels=16)
            self.assertLessEqual(Fraction(str(abs(coefficients[0][29] * value).upper().fmpq())), bound)

    def test_contour_geometry_refuses_carrier_crossing_and_singular_edge(self):
        for options in ({"threshold": 3}, {"threshold": 128, "edge_delta": 0},
                        {"threshold": 128, "shift": 0}, {"threshold": 128, "cells": 0}):
            with self.assertRaises(ValueError):
                tail.get_contour_family_bounds([Fraction(2)], [Fraction(3)], [acb(1)], **options)

    def test_zero_coefficient_and_inflated_coefficient_uncertainty(self):
        zero = tail.get_family_budgets([Fraction(2)], [acb(0)])
        self.assertTrue(all(value == 0 for value in zero[0].values()))
        uncertain = tail.get_family_budgets([Fraction(2)], [acb(arb(0, 1), arb(0, 1))])
        self.assertTrue(all(value > 0 for value in uncertain[0].values()))

    def test_healthy_shell_uses_actual_inclusive_tail_threshold(self):
        self.assertEqual(tail.get_healthy_shell_for_threshold(128, 39)["minimum_shell_index"], 6)
        self.assertEqual(tail.get_healthy_shell_for_threshold(Fraction(12801, 100), 39)["minimum_shell_index"], 7)
        self.assertEqual(tail.get_healthy_shell_for_threshold(64, 39)["minimum_shell_index"], 6)

    def test_invalid_dimensions_and_parameters_are_rejected(self):
        for arguments in ((self.budgets, [], 5), (self.budgets, [Fraction(3)], -1)):
            with self.assertRaises(ValueError):
                tail.get_tail_upper(*arguments)
        with self.assertRaises(ValueError):
            tail.get_whole_line_constant(self.budgets, [Fraction(3)], 3)
        with self.assertRaises(ValueError):
            tail.get_family_budgets([Fraction(0)], [acb(1)])
        with self.assertRaises(ValueError):
            tail.get_threshold_ladder(self.budgets, [Fraction(3)], start=True)

    def test_scope_flags_do_not_claim_a_gate_or_health(self):
        for flag in ("actual_numeric_coefficients_imported_in_lean", "tail_supplier_imported_in_lean",
                     "fourth_order_spectral_tail_instantiated", "rho_is_source_zero_proved",
                     "actual_gate_row_paired", "complete_zero_prefix_instantiated", "full_signed_kernel_priced",
                     "healthy_detector_instantiated", "owner_changed", "map103_reopened", "producer_go", "rh_claim"):
            self.assertFalse(self.result[flag])


if __name__ == "__main__":
    unittest.main(verbosity=2)
