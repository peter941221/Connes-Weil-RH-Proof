"""Artifact and interface controls for 2305 (M2 cap / kernel interval probe).

Keeps the committed artifact honest: the three verdicts and their
directional lower bounds must be internally consistent, the precision
control must agree with float64 inside the trusted zone and disagree
outside it, and every route failure factor must reproduce from the stored
quantities.
"""
import json
import math
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
ART = ROOT / "results" / "2305_hgap_trapz_m2_probe.json"
BUDGET = 1.0e7
WIN_LEN = 80.0
DESIGN_H = 0.02


class TrapzM2Controls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.art = json.loads(ART.read_text(encoding="utf-8"))

    def test_scope_and_verdicts(self):
        self.assertFalse(self.art["certificate"])
        self.assertEqual(self.art["p4_verdict"], "M2-CAP-FAILED")
        self.assertEqual(self.art["p4_panel_local_verdict"],
                         "PANEL-LOCAL-FAILED")
        self.assertEqual(self.art["p3_verdict"],
                         "KERNEL-INTERVAL-FAILED-NEEDS-GROUPING")
        self.assertEqual(self.art["prime_power_count"], 41136)

    def test_m2_route_reproduces(self):
        route = self.art["global_route"]
        m2 = route["M2_lower_bound_trusted_zone"]
        predicted = m2 * WIN_LEN * DESIGN_H ** 2 / 12.0
        self.assertAlmostEqual(route["bound_at_h_1_50_from_lower_bound"],
                               predicted, delta=1e-9 * predicted)
        self.assertAlmostEqual(route["cap_failure_factor"],
                               predicted / BUDGET,
                               delta=1e-9 * route["cap_failure_factor"])
        self.assertGreater(route["cap_failure_factor"], 1.0)
        # the trusted-zone sup sits below the untrusted full-window sup
        rows = {r["h"]: r for r in self.art["m2_rows"]}
        for row in rows.values():
            self.assertLessEqual(row["sup_by_region"]["abs_x_le_1.0"],
                                 row["sup_abs_Gi2_dense_window"])

    def test_panel_local_mass_law(self):
        rows = {r["h"]: r for r in self.art["m2_rows"]}
        self.assertEqual(sorted(rows), [0.005, 0.02])
        hi, lo = rows[0.02], rows[0.005]
        m_hi = hi["mass_by_region"]["abs_x_le_1.0"]
        m_lo = lo["mass_by_region"]["abs_x_le_1.0"]
        # mass ~ h^2: the two rows must agree within 25%
        self.assertAlmostEqual(m_lo * 16.0, m_hi, delta=0.25 * m_hi)
        route = self.art["panel_local_route"]
        self.assertGreater(route["failure_factor_at_design_h_0.02_from_lower_bound"],
                           1.0)
        self.assertAlmostEqual(
            route["required_h_upper_bound_from_lower_bound"],
            math.sqrt(BUDGET / route["quadratic_coefficient_trusted_zone"]),
            delta=1e-9 * route["required_h_upper_bound_from_lower_bound"])

    def test_p3_charge_and_verdict(self):
        p3 = self.art["p3"]
        self.assertGreater(p3["over_budget_trusted_zone"], 1.0)
        self.assertGreater(p3["integrated_kernel_squared_interval_error"],
                           p3["integrated_kernel_interval_error"])
        # the exact arc rule keeps at most the triangle width per cell
        self.assertLessEqual(p3["prime_width_max"], p3["prime_triangle_width"])
        self.assertLessEqual(p3["prime_width_mean"], p3["prime_width_max"])
        self.assertAlmostEqual(p3["sigma_slope_charge_per_cell"],
                               p3["sigma_prime_cap"] * p3["h"], delta=1e-12)

    def test_precision_control(self):
        prec = self.art["precision"]
        ctrl = self.art["gl_control"]
        self.assertGreater(prec["noise_floor_corr"], prec["noise_floor_base"])
        # inside the trusted zone float64 and mpmath agree
        b64 = ctrl["abs_B_40x16"][0]
        self.assertLess(abs(b64 / prec["abs_B_mp_1.0"] - 1.0), 1e-6)
        c64 = ctrl["abs_C_40x16"][0]
        self.assertLess(abs(c64 / prec["abs_C_mp_1.0"] - 1.0), 1e-5)
        # outside it the corr transform is float64 noise: order of magnitude
        self.assertLess(prec["abs_C_mp_4.0"], 1e-14)
        self.assertGreater(ctrl["abs_C_40x16"][2], 100.0 * prec["abs_C_mp_4.0"])
        self.assertLess(abs(ctrl["abs_B_40x16"][2] / prec["abs_B_mp_4.0"] - 1.0),
                        1e-4)

    def test_declaration_surface(self):
        self.assertEqual(self.art["budget"], BUDGET)
        self.assertEqual(self.art["window"], [-40.0, 40.0])
        self.assertEqual(self.art["dense_window"], [-4.0, 4.0])
        self.assertAlmostEqual(self.art["ann_coeffs"][4], (2 * math.pi) ** 4,
                               delta=1e-6)
        self.assertAlmostEqual(self.art["trusted_zone"]["abs_x_le"], 1.0)


if __name__ == "__main__":
    unittest.main()