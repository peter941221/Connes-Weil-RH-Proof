"""Artifact controls for 2303: corrected-owner centered-strip envelope.

Checks the committed artifact against its own invariants, the frozen
constants and the anchors that 2303 claims to reproduce.  Independent
numerical controls live in the per-mode runs; this file is the gate that
keeps the artifact honest after any regeneration.
"""
import json
import math
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
ART = ROOT / "results" / "2303_corrected_strip_envelope.json"
FROZEN_B = 9506275.102584327
RAW_B_2277 = 337039.47691484215


class CorrectedStripControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.art = json.loads(ART.read_text(encoding="utf-8"))

    def test_scope_flags(self):
        self.assertEqual(self.art["status"], "CORRECTED-STRIP-COVERED")
        self.assertTrue(self.art["gate"]["zero_free"])
        self.assertTrue(self.art["centered"]["covered"])
        self.assertNotIn("certificate", self.art)
        self.assertTrue(all("not a Lean certificate" in c
                            for c in self.art["nonclaims"][:1]))

    def test_owner_anchors(self):
        owner = self.art["owner"]
        self.assertEqual(owner["physical_profile"], "phi_(a^2)(y) exp(i theta y)")
        self.assertEqual(owner["families"], 30)
        self.assertTrue(owner["anchors"]["families_bitwise"])
        self.assertTrue(owner["anchors"]["base_bitwise"])
        self.assertTrue(owner["anchors"]["corr_bitwise"])

    def test_zero_count_gate(self):
        zero = self.art["gate"]["zero_count"]
        self.assertEqual(len(zero), 4)
        for channel, verdict in zero.items():
            self.assertEqual(verdict, "ZERO-FREE-CERTIFIED", channel)
        self.assertEqual(self.art["gate"]["edge"], "EDGE-ZERO-FREE-CERTIFIED")

    def test_centered_certificate(self):
        c = self.art["centered"]
        self.assertEqual(c["frozen"], FROZEN_B)
        self.assertEqual(c["max_point_sigma"], -0.5)
        self.assertEqual(c["max_point_binding"], "a")
        # the certified sup is the grid maximum times the sigma transfer
        transfer = self.art["grid"]["transfer"]
        self.assertAlmostEqual(c["sup_certified"], c["max_point_B"] * transfer,
                               delta=1e-6 * c["sup_certified"])
        self.assertLess(c["sup_certified"], FROZEN_B)
        self.assertAlmostEqual(c["margin"], FROZEN_B / c["sup_certified"],
                               delta=1e-6 * c["margin"])

    def test_raw_row_reproduction(self):
        rows = {r["sigma"]: r for r in self.art["grid_rows"]}
        self.assertEqual(len(rows), 101)
        row = rows[-0.5]
        self.assertEqual(row["raw_check"]["raw_B"], RAW_B_2277)
        self.assertTrue(self.art["anchor_raw"]["upper_ok"])
        for r in self.art["grid_rows"]:
            self.assertGreaterEqual(r["raw_check"]["v_min_over_raw"], 1.0)

    def test_ladder_and_inflation_shape(self):
        panel = self.art["panel"]
        self.assertEqual(len(panel["ladder_base"]), 5)
        self.assertEqual(len(panel["ladder_corr"]), 5)
        # the 2238 ladder majorants are monotone in the order
        for key in ("ladder_base", "ladder_corr"):
            vals = panel[key]
            self.assertTrue(all(b > a for a, b in zip(vals, vals[1:])))
        self.assertEqual(self.art["inflation"]["radii"]["base"],
                         1005486.289224448)
        self.assertEqual(self.art["inflation"]["radii"]["corr"],
                         2057069012.526474)
        self.assertEqual(self.art["grid"]["x_nodes"], 240001)
        self.assertEqual(self.art["grid"]["sigma_nodes"], 101)

    def test_provenance_paths_exist(self):
        for key, name in self.art["provenance"].items():
            if key in ("machinery",):
                continue
            self.assertTrue((ROOT / name).exists(), name)
        for name in self.art["provenance"]["machinery"]:
            self.assertTrue((ROOT / "scripts" / name).exists(), name)


if __name__ == "__main__":
    unittest.main()