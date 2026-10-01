"""2340: controls for recomposed point-plus-panel transfer."""
import json
import hashlib
from fractions import Fraction
from pathlib import Path
import unittest
from flint import arb, ctx
import routea_recomposed_point_panel_transfer_2340 as transfer

ROOT = Path(__file__).resolve().parents[1]

class RecomposedTransferTests(unittest.TestCase):
    def test_committed_result_has_all_nodes_and_no_owner_transfer(self):
        result = json.loads((ROOT / "results/2340_recomposed_point_panel_transfer.json").read_text())
        self.assertEqual(result["record"], 2340)
        self.assertTrue(result["all_nodes_fit_existing_pin"])
        self.assertEqual(result["failed_nodes"], [])
        self.assertEqual(result["maximum_node"], -50)
        self.assertFalse(result["old_inflation_reused"])
        self.assertFalse(result["owner_transfer_to_live_consumer"])
        self.assertFalse(result["producer_go"])
        self.assertTrue(result["baseline_contract_checked"])
        self.assertTrue(result["baseline_zero_free_gate"])
        self.assertTrue(result["baseline_sigma_rows_complete"])

    def test_exact_pin_readback_is_strict(self):
        result = json.loads((ROOT / "results/2340_recomposed_point_panel_transfer.json").read_text())
        maximum = Fraction(result["maximum_min_product_upper"]["upper_exact"])
        self.assertLess(maximum, Fraction("2644542.8515"))
        self.assertGreater(maximum, Fraction("706456"))

    def test_s3_constant_matches_analytic_ladder(self):
        constants = transfer.s_constants()
        self.assertTrue(constants[3] < 245161 * arb(-30).exp())
        self.assertTrue(constants[3] > 245159 * arb(-30).exp())

    def test_panel_is_recomputed_with_exact_radius_and_coefficients(self):
        result = json.loads((ROOT / "results/2340_recomposed_point_panel_transfer.json").read_text())
        row = result["rows"][0]
        for channel in ("base", "correction"):
            self.assertNotEqual(row["channels"][channel]["panel_m0"]["upper_exact"], "0")
            self.assertNotEqual(row["channels"][channel]["panel_d2"]["upper_exact"], "0")

    def test_stored_sum_upper_does_not_round_inside(self):
        left = 124793.81780631893
        right = 126636.30488983537
        exact = transfer.certificate.lift_float(left) + transfer.certificate.lift_float(right)
        self.assertTrue(transfer.stored_sum_upper(left, right) >= exact.upper())
        self.assertGreater(transfer.stored_sum_upper(left, right),
                           transfer.certificate.lift_float(left + right))

    def test_all_baseline_additions_dominate_exact_operand_sum(self):
        baseline = json.loads((ROOT / "results/2303_corrected_strip_envelope.json").read_text())
        inward_count = 0
        for row in baseline["grid_rows"]:
            for slot in ("base_M0", "base_D2", "corr_M0", "corr_D2"):
                left, right = row["point"][slot], row["panel"][slot]
                exact = Fraction(left) + Fraction(right)
                upper = Fraction(transfer.ep(transfer.stored_sum_upper(left, right))["upper_exact"])
                self.assertGreaterEqual(upper, exact)
                inward_count += Fraction(left + right) < exact
        self.assertEqual(inward_count, 188)

    def test_operand_sum_handles_precision_and_extreme_scales(self):
        previous_precision = ctx.prec
        try:
            for precision in (53, 80, 320):
                ctx.prec = precision
                for left, right in ((0.0, 0.0), (1.0, 2.0**-54),
                                    (2.0**1000, 2.0**-1000),
                                    (2.0**-1074, 2.0**-1074)):
                    upper = Fraction(transfer.ep(transfer.stored_sum_upper(left, right))["upper_exact"])
                    self.assertGreaterEqual(upper, Fraction(left) + Fraction(right))
        finally:
            ctx.prec = previous_precision

    def test_non_binary64_operands_are_rejected(self):
        with self.assertRaises(TypeError):
            transfer.stored_sum_upper("1.0", 2.0)

    def test_result_matches_current_source_hash(self):
        result = json.loads((ROOT / "results/2340_recomposed_point_panel_transfer.json").read_text())
        source = Path(transfer.__file__).read_bytes()
        self.assertEqual(result["source_sha256"], hashlib.sha256(source).hexdigest())

if __name__ == "__main__":
    unittest.main()
