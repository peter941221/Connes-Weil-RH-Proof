"""Artifact and mechanism controls for 2309 (certified transform-side majorant).

Locks the committed certificate: verdict and scope flags, the three-rung
dyadic ladder (denominators 64/128/256), the mechanically counted float64
budget table, the dps-100 reference dominance control, the subsample
sandwich against the stored-jet witness and the model-grade T, the
cross-record agreement with the 2308 weight side, the closure witness
joining the 2307 tail, and provenance.

The mechanism checks re-run instrument functions, not just the JSON: the
exact-rational float enclosure, the exact delta powers, the L1 modulus
convention, and the compiled operation counts.
"""
import json
import sys
import unittest
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import routea_hgap_transform_cert_2309 as instrument  # noqa: E402

ART = ROOT / "results" / "2309_hgap_transform_certified.json"
REF = ROOT / "results" / "2309_reference_controls.json"
PREDECESSOR = ROOT / "results" / "2308_window_weight_certified.json"
TAIL = ROOT / "results" / "2307_hgap_tail_certified.json"
BUDGET = 1.0e7
DENOMS = [64, 128, 256]
CHARGES = {64: 863819.2915438175, 128: 571815.9145338645,
           256: 477248.9858117574}
CERT_OVER_BUDGET = {64: 0.08638192915438175, 128: 0.05718159145338645,
                    256: 0.04772489858117574}
COUNTS = {0: 546, 1: 609, 2: 673, 3: 736, 4: 800, 5: 863, 6: 927}
BUDGET_UPPER = {
    "base": [6.130417746793512e-14, 2.532002553832731e-12,
             1.0458151135595221e-10, 4.319376036809869e-09,
             1.7840365319465696e-07, 7.368209596686087e-06,
             0.00030432438359542216],
    "corr": [9.95627332455112e-11, 4.112168293523837e-09,
             1.6984847603560522e-07, 7.015001291957461e-06,
             0.00028974135314571085, 0.011966543176532762,
             0.49424637399080334],
}
WORST_REFERENCE = 0.0009617244943841909
CROSS_2308 = 0.9999999991369299
MARGIN = 20.953423259749634


def load_step(denom):
    return json.loads(
        (ROOT / "results" /
         f"2309_transform_step_den{denom}.json").read_text(encoding="utf-8"))


class TransformSideCertifiedControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.art = json.loads(ART.read_text(encoding="utf-8"))
        cls.rows = {row["step_denom"]: row for row in cls.art["rows"]}
        cls.steps = {denom: load_step(denom) for denom in DENOMS}
        cls.ref = json.loads(REF.read_text(encoding="utf-8"))
        cls.predecessor = json.loads(
            PREDECESSOR.read_text(encoding="utf-8"))
        cls.tail = json.loads(TAIL.read_text(encoding="utf-8"))

    def test_scope_and_verdict(self):
        self.assertEqual(self.art["status"], "TRANSFORM-SIDE-CERTIFIED")
        self.assertTrue(self.art["transform_certificate"])
        self.assertTrue(self.art["window_certificate"])
        self.assertTrue(self.art["certificate"])
        self.assertTrue(self.art["hgap_closed"])
        self.assertFalse(self.art["rh_claim"])
        self.assertFalse(self.art["producer_go"])
        self.assertEqual(self.art["budget"], BUDGET)
        self.assertEqual(self.art["taylor_degree"], 6)
        self.assertEqual(self.art["interval"]["lib"], "mpmath.iv")
        self.assertEqual(self.art["interval"]["dps"], 80)

    def test_ladder_locked_and_monotone(self):
        self.assertEqual(sorted(self.rows), DENOMS)
        for denom in DENOMS:
            row = self.rows[denom]
            self.assertAlmostEqual(row["charge_hi"], CHARGES[denom],
                                   delta=abs(CHARGES[denom]) * 1e-12)
            self.assertAlmostEqual(row["cert_over_budget"],
                                   CERT_OVER_BUDGET[denom], places=9)
            # window |xi| <= 40 on dyadic cells of width 1/denom
            self.assertEqual(row["cell_count"], 80 * denom)
        self.assertGreater(CHARGES[64], CHARGES[128])
        self.assertGreater(CHARGES[128], CHARGES[256])
        self.assertEqual(self.art["best"]["step_denom"], 256)
        self.assertAlmostEqual(self.art["best"]["charge_hi"], CHARGES[256],
                               delta=CHARGES[256] * 1e-12)

    def test_budget_clearance(self):
        for denom in DENOMS:
            self.assertLess(self.rows[denom]["cert_over_budget"], 0.09)
        self.assertLess(self.art["best"]["cert_over_budget"], 0.05)

    def test_budget_table_locked(self):
        budgets = self.steps[64]["budget_upper_by_order"]
        for channel in ("base", "corr"):
            for order in range(7):
                self.assertAlmostEqual(
                    budgets[channel][order], BUDGET_UPPER[channel][order],
                    delta=abs(BUDGET_UPPER[channel][order]) * 1e-12,
                    msg=f"{channel} order {order} budget moved")

    def test_budgets_pointwise_below_model_errors(self):
        ratios = self.steps[64]["budget_over_model_by_order"]
        for channel in ("base", "corr"):
            for order, ratio in enumerate(ratios[channel]):
                self.assertLessEqual(ratio, 1.0,
                                     f"{channel} order {order} looser")
            self.assertAlmostEqual(ratios[channel][0], 0.5989, places=3)
            self.assertLess(ratios[channel][6], 0.05)

    def test_subsample_sandwich(self):
        for denom in DENOMS:
            controls = self.rows[denom]["controls"]
            self.assertTrue(controls["order_zero_bitwise"])
            self.assertLessEqual(controls["cross_path_max_ratio"], 1.0)
            # certified >= stored-jet witness (>= 1) and <= model-grade T
            self.assertGreaterEqual(controls["pure_witness_min_margin"], 1.0)
            self.assertLessEqual(controls["model_grade_max_margin"], 1.0)
            self.assertAlmostEqual(controls["pure_witness_min_margin"], 1.0,
                                   delta=1e-8)
            self.assertAlmostEqual(controls["model_grade_max_margin"], 1.0,
                                   delta=1e-8)

    def test_reference_dominance(self):
        self.assertTrue(self.ref["dominates"])
        self.assertAlmostEqual(self.ref["worst_allowance_ratio"],
                               WORST_REFERENCE, delta=1e-15)
        self.assertEqual(len(self.ref["rows"]), 24)
        for row in self.ref["rows"]:
            self.assertLessEqual(row["allowance_ratio"], WORST_REFERENCE * 1.001)
            self.assertLessEqual(row["absolute_error"], row["budget_upper"])
            self.assertAlmostEqual(
                row["allowance_ratio"],
                row["absolute_error"] / row["budget_upper"], places=12)
        worst = max(self.ref["rows"], key=lambda r: r["allowance_ratio"])
        self.assertEqual((worst["order"], worst["channel"]), (0, "base"))
        self.assertAlmostEqual(worst["xi"], -3.605, places=6)

    def test_reference_budgets_match_ladder(self):
        for row in self.ref["rows"]:
            self.assertAlmostEqual(
                row["budget_upper"], BUDGET_UPPER[row["channel"]][row["order"]],
                delta=abs(BUDGET_UPPER[row["channel"]][row["order"]]) * 1e-12)

    def test_cross_record_against_2308(self):
        cross = self.art["cross_record"]
        self.assertAlmostEqual(
            cross["2308_window_weight_certified_charge"],
            self.predecessor["best"]["charge_hi"],
            delta=self.predecessor["best"]["charge_hi"] * 1e-12)
        self.assertAlmostEqual(cross["cert_over_2308_charge"],
                               CROSS_2308, delta=1e-12)
        # the certified transform side is a hair TIGHTER than the 2308
        # charge (whose T side was the model-grade majorant)
        self.assertLess(cross["cert_over_2308_charge"], 1.0)

    def test_closure_witness(self):
        closure = self.art["closure"]
        self.assertAlmostEqual(closure["tail_best_upper_2307"],
                               self.tail["best"]["tail_upper"], places=36)
        self.assertEqual(closure["tail_best_order_2307"],
                         self.tail["best"]["order"])
        self.assertEqual(closure["tail_cheapest_rung_order_2307"], 16)
        self.assertLess(closure["sum"], BUDGET)
        self.assertTrue(closure["closed"])
        self.assertTrue(closure["cheapest_rung_closed"])
        self.assertAlmostEqual(closure["margin"], MARGIN, delta=1e-9)
        self.assertAlmostEqual(
            closure["sum"],
            closure["window_charge_hi"] + closure["tail_best_upper_2307"],
            delta=1e-6)

    def test_cell_geometry(self):
        for denom in DENOMS:
            step = self.steps[denom]
            self.assertEqual(step["midpoint_coordinate_gap"]["lower"], "0")
            self.assertEqual(step["midpoint_coordinate_gap"]["upper"], "0")
            radius = step["coverage_radius"]
            self.assertEqual(radius["lower"], radius["upper"])
            self.assertAlmostEqual(float(radius["upper"]), 1.0 / (2 * denom),
                                   places=12)
            self.assertEqual(step["prime_power_count"], 41136)
            self.assertEqual(step["prime_limit"], 492475)

    def test_charge_interval_cohesive(self):
        for denom in DENOMS:
            charge = self.steps[denom]["charge_render"]
            lower = float(charge["lower"])
            upper = float(charge["upper"])
            self.assertLessEqual(lower, upper)
            self.assertLessEqual((upper - lower) / upper, 1e-30)
            self.assertAlmostEqual(
                upper, self.steps[denom]["charge_hi"],
                delta=abs(self.steps[denom]["charge_hi"]) * 1e-15)

    def test_mechanism_exact_float_enclosure(self):
        for value in (0.1, -3.605, 1.0 / 3.0):
            iv = instrument.float_point_iv(value)
            numerator, denominator = value.as_integer_ratio()
            self.assertEqual(denominator & (denominator - 1), 0)
            self.assertEqual(Fraction(numerator, denominator), Fraction(value))
            self.assertAlmostEqual(float(iv.a), value, delta=0.0)
            self.assertAlmostEqual(float(iv.b), value, delta=0.0)

    def test_mechanism_delta_powers_exact(self):
        import math
        powers = instrument.delta_powers(128)
        self.assertEqual(len(powers), 7)
        for k in range(7):
            expected = 1.0 / (256 ** k) / math.factorial(k)
            self.assertAlmostEqual(float(powers[k].a), expected,
                                   delta=expected * 1e-12)
            self.assertAlmostEqual(float(powers[k].b), expected,
                                   delta=expected * 1e-12)

    def test_mechanism_l1_modulus_and_counts(self):
        modulus = instrument.l1_modulus_iv(3.0, -4.0)
        self.assertAlmostEqual(float(modulus.b), 7.0, delta=0.0)
        for k in range(7):
            self.assertEqual(instrument.compiled_counts(k, 15), COUNTS[k])
            if k:
                self.assertGreater(instrument.compiled_counts(k, 15),
                                   instrument.compiled_counts(k - 1, 15))

    def test_step_json_matches_reduced_artifact(self):
        for denom in DENOMS:
            step = self.steps[denom]
            row = self.rows[denom]
            for key in ("cell_count", "charge_hi", "cert_over_budget",
                        "t_sum_max", "t_sum_mean", "max_cell_sup_base",
                        "max_cell_sup_corr", "controls",
                        "budget_over_model_by_order"):
                self.assertEqual(step[key], row[key], f"{denom}:{key}")

    def test_provenance(self):
        provenance = self.art["provenance"]
        self.assertEqual(provenance["script"],
                         "scripts/routea_hgap_transform_cert_2309.py")
        self.assertEqual(provenance["weight_factor"],
                         "results/2308_window_weight_certified.json")
        self.assertEqual(provenance["tail"],
                         "results/2307_hgap_tail_certified.json")
        self.assertEqual(provenance["owner_capture"],
                         "results/2275_gap_owner_audit.json")
        self.assertEqual(len(provenance["radii_ledger"]), 2)


if __name__ == "__main__":
    unittest.main(verbosity=2)