"""2341: analytic controls and provenance mutation tests."""
import copy
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import unittest

from flint import arb, ctx

import routea_one_sided_panel_transfer_2341 as panel

ROOT = Path(__file__).resolve().parents[1]


class OneSidedPanelTests(unittest.TestCase):
    def test_concave_quadratic_attains_chord_allowance(self):
        radius = arb(1)
        bound = panel.get_panel_upper([arb(1), arb(2), arb(2)], 0, arb(0), radius, 2)
        self.assertGreaterEqual(Fraction(str(bound.fmpq())), Fraction(4, 3))
        self.assertLess(Fraction(str(bound.fmpq())), Fraction(4, 3) + Fraction(1, 10**12))

    def test_zero_crossing_does_not_require_zero_free_gate(self):
        bound = panel.get_panel_upper([arb(1), arb(1), arb(0)], 0, arb(0), arb(1), 2)
        self.assertTrue(bound.is_zero())
        left, right = Fraction(-1), Fraction(1)
        trapezoid = (right - left) * (abs(left) + abs(right)) / 2
        integral = (left**2 + right**2) / 2
        self.assertLess(integral, trapezoid)

    def test_complex_rotation_has_large_modulus_curvature_but_zero_one_sided_error(self):
        tiny = Fraction(1, 10**6)
        norm_second_at_zero = 1 / tiny
        self.assertGreater(norm_second_at_zero, 100000)
        bound = panel.get_panel_upper([arb(2), arb(1), arb(0)], 0, arb(0), arb(1), 2)
        self.assertTrue(bound.is_zero())
        midpoint = arb(str(tiny.numerator)) / tiny.denominator
        endpoint = (1 + midpoint**2).sqrt()
        self.assertLess(midpoint, endpoint)

    def test_refinement_scales_panel_quadratically(self):
        ladder = [arb(1), arb(2), arb(3)]
        coarse = panel.get_panel_upper(ladder, 0, arb(0), arb(1), 3)
        fine = panel.get_panel_upper(ladder, 0, arb(0), arb(1), 5)
        self.assertTrue(coarse.overlaps(4 * fine))

    def test_negative_sigma_gives_same_global_majorant(self):
        ladder = [arb(1), arb(2), arb(3)]
        self.assertEqual(panel.recomposed.ep(panel.get_panel_upper(ladder, 0, arb("1/2"), arb(1), 5)),
                         panel.recomposed.ep(panel.get_panel_upper(ladder, 0, arb("-1/2"), arb(1), 5)))

    def test_invalid_grid_is_rejected(self):
        for radius, count in ((0, 3), (1, 1)):
            with self.assertRaises(ValueError):
                panel.get_coordinate_gap(float(radius), count)
            with self.assertRaises(ValueError):
                panel.get_panel_upper([arb(1)] * 3, 0, arb(0), arb(radius), count)

    def test_exact_dyadic_grid_has_no_coordinate_gap(self):
        self.assertEqual(panel.get_coordinate_gap(1.0, 5), Fraction(0))

    def test_node_sum_mutations_are_rejected(self):
        baseline = json.loads((ROOT / "results/2303_corrected_strip_envelope.json").read_text())
        source = baseline["grid_rows"][0]
        point = json.loads((ROOT / "results/2303_sigma_-50.json").read_text())
        panel.validate_node_sum(source, point, 240001)
        for key, value in (("sigma_index", -49), ("nodes", 2), ("mode", "fake")):
            wrong = copy.deepcopy(point)
            wrong[key] = value
            with self.assertRaises(ValueError):
                panel.validate_node_sum(source, wrong, 240001)

    def test_baseline_contract_mutations_are_rejected(self):
        baseline = json.loads((ROOT / "results/2303_corrected_strip_envelope.json").read_text())
        for section, key, value in (("gate", "zero_free", False),
                                    ("centered", "covered", False),
                                    ("grid", "sigma_nodes", 100)):
            wrong = copy.deepcopy(baseline)
            wrong[section][key] = value
            with self.assertRaises(ValueError):
                panel.recomposed.validate_baseline_contract(wrong)
        wrong = copy.deepcopy(baseline)
        wrong["grid_rows"].reverse()
        with self.assertRaises(ValueError):
            panel.recomposed.validate_baseline_contract(wrong)

    def test_derivative_ladder_dominates_exact_bump_polynomials(self):
        polynomial = {0: 1}
        constants = panel.recomposed.s_constants()
        for order in range(5):
            coefficient_sum = sum(abs(value) for value in polynomial.values())
            reference = (coefficient_sum * arb(-30).exp()).upper()
            self.assertTrue(constants[order].upper() >= reference)
            next_polynomial = {}
            for power, value in polynomial.items():
                terms = [(power + 1, -60 * value),
                         (power + 1, 4 * order * value),
                         (power + 3, -4 * order * value)]
                if power:
                    terms += [(power - 1, power * value),
                              (power + 1, -2 * power * value),
                              (power + 3, power * value)]
                for exponent, coefficient in terms:
                    next_polynomial[exponent] = next_polynomial.get(exponent, 0) + coefficient
            polynomial = {power: value for power, value in next_polynomial.items() if value}

    def test_committed_result_retains_open_obligations_and_source_identity(self):
        result = json.loads((ROOT / "results/2341_one_sided_panel_transfer.json").read_text())
        self.assertEqual(result["source_sha256"], hashlib.sha256(Path(panel.__file__).read_bytes()).hexdigest())
        self.assertFalse(result["point_node_upper_theorem_proved"])
        self.assertFalse(result["coordinate_grid_identity_with_original_run_proved"])
        self.assertFalse(result["transfer_theorem_imported_in_lean"])
        self.assertFalse(result["zero_count_used_by_new_panel_law"])
        self.assertFalse(result["owner_transfer_to_live_consumer"])
        self.assertFalse(result["producer_go"])
        self.assertFalse(result["rh_claim"])
        self.assertTrue(result["all_nodes_fit_existing_pin"])
        self.assertEqual(len(result["rows"]), 101)
        self.assertEqual(len(result["node_sum_provenance"]), 101)
        for name, digest in result["input_sha256"].items():
            filename = {"baseline": "2303_corrected_strip_envelope.json",
                        "recomposed": "2340_recomposed_point_panel_transfer.json",
                        "repair": "2338_exact_interpolation_repair.json"}[name]
            self.assertEqual(digest, hashlib.sha256((ROOT / "results" / filename).read_bytes()).hexdigest())
        for name, digest in result["helper_source_sha256"].items():
            self.assertEqual(digest, hashlib.sha256((ROOT / "scripts" / name).read_bytes()).hexdigest())
        for entry in result["node_sum_provenance"]:
            self.assertEqual(entry["sha256"], hashlib.sha256(
                (ROOT / "results" / entry["name"]).read_bytes()).hexdigest())
        parent = json.loads((ROOT / "results/2340_recomposed_point_panel_transfer.json").read_text())
        parent_rows = {row["j"]: row for row in parent["rows"]}
        for row in result["rows"]:
            upper = Fraction(row["min_product_upper"]["upper_exact"])
            self.assertTrue(row["fits_existing_pin"])
            self.assertLess(upper, panel.recomposed.PIN)
            previous = Fraction(parent_rows[row["j"]]["min_product_upper"]["upper_exact"])
            self.assertGreaterEqual(upper, previous)


if __name__ == "__main__":
    ctx.prec = 320
    unittest.main()
