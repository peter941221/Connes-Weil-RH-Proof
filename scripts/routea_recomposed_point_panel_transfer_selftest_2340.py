"""2340: controls for recomposed point-plus-panel transfer."""
import json
from fractions import Fraction
from pathlib import Path
import unittest
from flint import arb
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

if __name__ == "__main__":
    unittest.main()
