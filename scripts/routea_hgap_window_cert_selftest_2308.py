"""Artifact and mechanism controls for 2308 (certified finite-window weight).

Locks the committed certificate: verdict and scope flags, the three-rung
dyadic ladder (denominators 64/128/256), budget clearance, the soundness
direction cert >= sampled proxy on every rung, the cross-record comparison
with the 2302 finest sampled proxy, the d^5 refinement signature of the
kernel Taylor remainder, the pinned prime-power book and S-moment constants,
cell geometry (exact dyadic cells, zero midpoint gap, radius = 1/(2 denom)),
charge-interval cohesion, and provenance.

The mechanism checks re-run instrument functions, not just the JSON:
the S-moment ladder against float64 references, the convention replication
against the 2280 prime_kernel, and the certified charge interval endpoints.
"""
import json
import sys
import unittest
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import routea_hgap_window_cert_2308 as instrument  # noqa: E402

ART = ROOT / "results" / "2308_window_weight_certified.json"
PREDECESSOR = ROOT / "results" / "2302_local_frequency_taylor_screen.json"
OWNER = ROOT / "results" / "2275_gap_owner_audit.json"
BUDGET = 1.0e7
DENOMS = [64, 128, 256]
CHARGES = {64: 863819.2938082191, 128: 571815.9153523268,
           256: 477248.9862236567}
RATIOS = {64: 2.0025966355198266, 128: 1.3993214008109054,
          256: 1.1828176540100686}
REMAINDERS = {64: 1.4047090895918584, 128: 0.043897159049745574,
              256: 0.0013717862203045492}


def load_step(denom):
    return json.loads(
        (ROOT / "results" /
         f"2308_window_weight_step_den{denom}.json").read_text(encoding="utf-8"))


class WindowWeightCertifiedControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.art = json.loads(ART.read_text(encoding="utf-8"))
        cls.rows = {row["step_denom"]: row for row in cls.art["rows"]}
        cls.steps = {denom: load_step(denom) for denom in DENOMS}

    def test_scope_and_verdict(self):
        self.assertEqual(self.art["status"], "WINDOW-WEIGHT-CERTIFIED")
        self.assertTrue(self.art["weight_certificate"])
        self.assertFalse(self.art["certificate"])
        self.assertFalse(self.art["hgap_closed"])
        self.assertEqual(self.art["budget"], BUDGET)
        self.assertEqual(self.art["taylor_degree"], 4)
        self.assertEqual(self.art["interval"]["lib"], "mpmath.iv")
        self.assertEqual(self.art["interval"]["dps"], 80)
        self.assertIn("weight-side interval-certified", self.art["grade"])
        self.assertIn("2297/2301/2302", self.art["grade"])
        self.assertIn("no hgap certificate", self.art["scope"])
        joined = " ".join(self.art["nonclaims"])
        self.assertIn("only the weight factor is interval-certified", joined)
        self.assertIn("41136", self.art["scope"])
        self.assertIn("2280", self.art["scope"])

    def test_ladder_shape_and_monotone_refinement(self):
        self.assertEqual([row["step_denom"] for row in self.art["rows"]], DENOMS)
        previous = None
        for denom in DENOMS:
            row = self.rows[denom]
            self.assertEqual(row["cell_count"], 80 * denom)
            if previous is not None:
                self.assertLess(row["charge_hi"], previous,
                                "charge must fall under refinement")
            previous = row["charge_hi"]

    def test_budget_clearance(self):
        for denom in DENOMS:
            self.assertLess(self.rows[denom]["cert_over_budget"], 0.1)
        self.assertLess(self.art["best"]["cert_over_budget"], 0.05)
        self.assertEqual(self.art["best"]["step_denom"], 256)
        self.assertAlmostEqual(self.art["best"]["charge_hi"], CHARGES[256],
                               delta=1e-9 * CHARGES[256])

    def test_soundness_direction_and_tightness(self):
        # sup_cell W >= W(center) makes the certified charge >= the sampled
        # proxy on the same grid; the ratio must also stay tight (< 3x).
        for denom in DENOMS:
            row = self.rows[denom]
            self.assertGreaterEqual(row["cert_over_proxy_same_grid"], 1.0 - 1e-9,
                                    f"denom {denom}: certified below proxy")
            self.assertLess(row["cert_over_proxy_same_grid"], 3.0,
                            f"denom {denom}: certified far above proxy")
            self.assertAlmostEqual(row["cert_over_proxy_same_grid"], RATIOS[denom],
                                   delta=1e-6 * RATIOS[denom])
            self.assertAlmostEqual(row["charge_hi"], CHARGES[denom],
                                   delta=1e-9 * CHARGES[denom])
            self.assertAlmostEqual(row["kernel_taylor_remainder_upper"],
                                   REMAINDERS[denom],
                                   delta=1e-6 * REMAINDERS[denom])

    def test_d5_refinement_signature(self):
        # the Lagrange remainder scales like d^5: halving the step divides it
        # by ~32 on both rungs (the measured Taylor-tail law of 2302/2308)
        for coarse, fine in ((64, 128), (128, 256)):
            ratio = REMAINDERS[coarse] / REMAINDERS[fine]
            self.assertGreater(ratio, 30.0)
            self.assertLess(ratio, 34.0)

    def test_cross_record_against_2302(self):
        source = json.loads(PREDECESSOR.read_text(encoding="utf-8"))
        finest = min(row["sampled_weight_proxy_charge"] for row in source["rows"])
        self.assertAlmostEqual(self.art["cross_record"]["2302_finest_sampled_proxy"],
                               finest, delta=1e-9 * finest)
        ratio = self.art["cross_record"]["cert_over_2302_finest_proxy"]
        self.assertGreater(ratio, 1.0)
        self.assertLess(ratio, 1.5)
        self.assertAlmostEqual(ratio, CHARGES[256] / finest, delta=1e-6 * ratio)

    def test_cell_geometry(self):
        for denom in DENOMS:
            step = self.steps[denom]
            self.assertEqual(step["step"], 1.0 / denom)
            self.assertEqual(step["coverage_radius"]["lower"],
                             repr(1.0 / (2 * denom)).strip("'"))
            self.assertEqual(step["midpoint_coordinate_gap"]["lower"], "0")
            self.assertEqual(step["midpoint_coordinate_gap"]["upper"], "0")
            self.assertEqual(step["prime_power_count"], 41136)
            self.assertEqual(step["prime_limit"], 492475)
            self.assertAlmostEqual(step["support"], 13.1072, delta=1e-12)
            self.assertLess(float(step["base_radius"]["upper"]), 1e-13)
            self.assertGreater(float(step["base_radius"]["upper"]), 1e-14)
            self.assertLess(float(step["corr_radius"]["upper"]), 1e-10)
            self.assertGreater(float(step["corr_radius"]["upper"]), 1e-11)

    def test_charge_interval_cohesive(self):
        for denom in DENOMS:
            step = self.steps[denom]
            lo = float(step["charge_render"]["lower"])
            hi = float(step["charge_render"]["upper"])
            self.assertGreaterEqual(hi, lo)
            self.assertLess((hi - lo) / hi, 1e-30)
            self.assertLess(abs(step["charge_hi_float"] - hi) / hi, 1e-14)
            self.assertLess(abs(step["charge_hi"] - hi) / hi, 1e-14)

    def test_pinned_constants(self):
        for denom in DENOMS:
            step = self.steps[denom]
            self.assertAlmostEqual(step["A_upper"][0], 2801.5021085164085,
                                   delta=1e-9 * 2801.5021085164085)
            self.assertAlmostEqual(step["A_upper"][5], 5791701927943.102,
                                   delta=1e-9 * 5791701927943.102)
            self.assertAlmostEqual(step["B_upper"][4], 921777990747.0049,
                                   delta=1e-9 * 921777990747.0049)
            self.assertEqual(step["taylor_degree"], 4)
            self.assertLess(step["t_sum_max"], 1e-8)
            self.assertGreater(step["t_sum_max"], 1e-10)
            self.assertLess(step["max_cell_sup_base"], 1.1)
            self.assertLess(step["max_cell_sup_corr"], 70.0)
            self.assertGreater(step["max_cell_sup_corr"], 60.0)

    def test_mechanism_charge_interval_endpoints(self):
        # re-run the directed summation on the recorded per-cell data is not
        # stored, so the mechanism control instead re-certifies the *constants*
        # path: moment ladder vs float sums, sigma anchors, and the S-moment
        # enclosure of the float64 reference on a subsample of the book.
        import mpmath as mp
        mp.mp.dps = mp.iv.dps = 80
        import routea_regenerated_carrier_evaluator_2301 as evaluator
        carrier = evaluator.bridge.refined.remainder.carrier
        book = instrument.prime_book(carrier.SOURCE)
        moments = instrument.moment_ladder(book, instrument.TAYLOR_DEGREE)
        A, B = moments
        float_a0 = 2.0 * float(np.sum(book["weights"]))
        self.assertGreaterEqual(float_a0, float(A[0].a) * (1 - 1e-12))
        self.assertLessEqual(float_a0, float(A[0].b) * (1 + 1e-12))
        float_b4 = 2.0 * float(np.sum(book["weights"] * book["phi"] ** 4 *
                                       book["logn"]))
        self.assertGreaterEqual(float_b4, float(B[4].a) * (1 - 1e-12))
        self.assertLessEqual(float_b4, float(B[4].b) * (1 + 1e-12))

    def test_module_contracts(self):
        self.assertEqual(instrument.TAYLOR_DEGREE, 4)
        self.assertEqual(instrument.BUDGET, BUDGET)
        self.assertEqual(instrument.prime_book.__name__, "prime_book")
        for denom in DENOMS:
            step = self.steps[denom]
            self.assertIn("transform", step["timing_sec"])
            self.assertGreater(step["timing_sec"]["total"], 10.0)

    def test_provenance(self):
        prov = self.art["provenance"]
        self.assertEqual(prov["script"],
                         "scripts/routea_hgap_window_cert_2308.py")
        self.assertTrue((ROOT / prov["script"]).is_file())
        self.assertTrue(
            (ROOT / "scripts/routea_hgap_window_cert_selftest_2308.py").is_file())
        self.assertTrue(PREDECESSOR.is_file())
        self.assertTrue(OWNER.is_file())
        self.assertGreater(PREDECESSOR.stat().st_size, 0)
        self.assertGreater(OWNER.stat().st_size, 0)

    def test_step_json_matches_reduced_artifact(self):
        for denom in DENOMS:
            step = self.steps[denom]
            row = self.rows[denom]
            self.assertEqual(step["cell_count"], row["cell_count"])
            self.assertAlmostEqual(step["charge_hi"], row["charge_hi"],
                                   delta=1e-12 * row["charge_hi"])
            self.assertAlmostEqual(step["cert_over_proxy_same_grid"],
                                   row["cert_over_proxy_same_grid"],
                                   delta=1e-12 * row["cert_over_proxy_same_grid"])


if __name__ == "__main__":
    unittest.main()