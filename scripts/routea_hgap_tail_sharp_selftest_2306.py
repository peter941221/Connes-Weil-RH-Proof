"""Artifact and mechanism controls for 2306 (grouped sharp flat-edge tail).

Locks the committed artifact: verdict and budget, the covered/dead ladder,
the best order at the tail minimum, the inflation ceilings that carry the
grouping claim, kappa-variation stability, the independent mpmath control
ratio, the 2304 cross-check ratios, and the u-space evaluation mechanism
itself (A_j against the Bell closed form, the j-sum against an independent
mpmath Leibniz arrangement, the ODE derivative identity by finite
differences, and the S-function cell-sup against brute force).

The mechanism checks re-run the instrument code, not just the JSON: the
contamination that killed the expanded-polynomial form (coefficient
magnitude sums up to ~1e16x the value) is exactly what the u-space path
avoids, so its correctness is asserted directly.
"""
import json
import math
import sys
import unittest
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import routea_hgap_tail_sharp_2306 as instrument  # noqa: E402

ART = ROOT / "results" / "2306_hgap_tail_sharp.json"
MP_CONTROL = ROOT / "results" / "2306_mp_control.json"
BUDGET = 1.0e7


class TailSharpControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.art = json.loads(ART.read_text(encoding="utf-8"))
        cls.rows = {r["order"]: r for r in cls.art["rows"]}

    def test_scope_and_verdict(self):
        self.assertEqual(self.art["status"], "TAIL-SHARP-COVERED")
        self.assertFalse(self.art["certificate"])
        self.assertEqual(self.art["budget"], BUDGET)
        self.assertEqual(self.art["xi0"], 40.0)
        self.assertEqual(self.art["kappa_log2_main"], 30)
        self.assertIn("grouped", self.art["mechanism"])
        self.assertIn("without boundary terms", self.art["mechanism"])

    def test_ladder_shape_and_coverage(self):
        orders = [r["order"] for r in self.art["rows"]]
        self.assertEqual(orders, [8, 12, 16, 20, 24, 28, 32, 36, 40, 44])
        self.assertEqual(self.art["orders_dead"], [8, 12])
        for order, row in self.rows.items():
            if order in self.art["orders_dead"]:
                self.assertGreater(row["tail_float"], BUDGET)
            else:
                self.assertLess(row["tail_float"], BUDGET)
        # every row carries the pinned inputs
        for row in self.art["rows"]:
            self.assertEqual(row["families"], 30)
            self.assertEqual(row["theta_groups"], 25)
            self.assertAlmostEqual(row["ann_l1"], 2497731.388738144,
                                   delta=1e-9 * row["ann_l1"])
            self.assertAlmostEqual(row["c_w"], 2810.1333609392077,
                                   delta=1e-12 * row["c_w"])

    def test_best_order_is_tail_minimum(self):
        bounds = {r["order"]: r["tail_float"] for r in self.art["rows"]}
        best = min(bounds, key=bounds.get)
        self.assertEqual(best, self.art["best_order"])
        self.assertEqual(self.art["best_order"], 36)
        self.assertAlmostEqual(self.art["best_tail_bound_float"],
                               bounds[best], delta=1e-6 * bounds[best])
        self.assertLess(bounds[best], 1e-30)
        self.assertGreater(float(self.art["best_margin"]), 1e30)

    def test_grouped_inflation_ceilings(self):
        # the grouping claim: the certified cell bound sits within a small
        # factor of the sampled sup -- the contamination that broke the
        # expanded-polynomial path (1e9+) must not come back.
        for order in (8, 12, 16, 20, 24, 28, 32):
            row = self.rows[order]
            self.assertLess(row["inflation_base"], 2.0)
            self.assertLess(row["inflation_corr"], 10.0)
        self.assertLess(self.rows[20]["inflation_base"], 1.01)
        self.assertLess(self.rows[20]["inflation_corr"], 5.0)
        # and the covered ladder really uses the sup, not a local sample
        for order in (16, 20, 24, 28, 32, 36):
            row = self.rows[order]
            self.assertGreater(row["ub_base"], row["lb_dense_base"] * 0.9)
            self.assertGreater(row["ub_corr"], row["lb_dense_corr"] * 0.5)

    def test_kappa_variation_stable(self):
        rows = self.art["controls"]["kappa_variation"]["rows"]
        self.assertEqual(len(rows), 9)
        by_key = {(r["order"], r["kappa_log2"]): r for r in rows}
        self.assertEqual(sorted({r["order"] for r in rows}), [20, 24, 28])
        for order in (20, 24, 28):
            coarse = by_key[(order, 24.0)]
            fine = by_key[(order, 36.0)]
            for channel in ("ub_base", "ub_corr"):
                ratio = coarse[channel] / fine[channel]
                self.assertLess(abs(ratio - 1.0), 1e-5)

    def test_mp_control_ratio(self):
        control = json.loads(MP_CONTROL.read_text(encoding="utf-8"))
        self.assertEqual(control["order"], self.art["best_order"])
        rows = {r["channel"]: r for r in control["rows"]}
        self.assertLess(rows["base"]["ub_over_mp"], 10.0)
        self.assertLess(rows["corr"]["ub_over_mp"], 1e8)
        for row in control["rows"]:
            self.assertGreater(float(row["mp_abs_T"]), 0.0)

    def test_2304_crosscheck(self):
        cc = self.art["controls"]["crosscheck_2304_N20"]
        self.assertEqual([r["order"] for r in cc["rows"]], [16, 20, 24, 28])
        for row in cc["rows"]:
            self.assertAlmostEqual(float(row["ratio"]), 1.0,
                                   delta=1e-6 + 1e-6 * abs(float(row["ratio"])))
        erratum = self.art["erratum_2304"]
        self.assertIn("length", erratum["missing_length_factor"])
        self.assertIn("416", erratum["price_arithmetic"])

    def test_A_j_against_bell_closed_form(self):
        import mpmath as mp
        mp.mp.dps = 40
        A = instrument.A_polys(8)
        worst = 0.0
        for u in (0.1, 0.37, 0.62, -0.44):
            um = mp.mpf(repr(u))
            s = 1 - um * um
            psi = mp.e ** (-instrument.K / s)
            L = []
            for m in range(1, 9):
                t = (1 - um) ** (-(m + 1))
                t = t + (1 + um) ** (-(m + 1)) if m % 2 == 0 else \
                    t - (1 + um) ** (-(m + 1))
                L.append(-instrument.K * mp.factorial(m) / 2 * t)
            Y = [mp.mpf(1)]
            for j in range(1, 9):
                acc = mp.mpf(0)
                for i in range(j):
                    acc += mp.binomial(j - 1, i) * Y[j - 1 - i] * L[i]
                Y.append(acc)
                aj = sum(mp.mpf(ck) * um ** k for k, ck in enumerate(A[j]))
                lhs = psi * Y[j]
                rhs = psi * aj * s ** (-2 * j)
                worst = max(worst, float(abs(lhs - rhs) / abs(lhs)))
        self.assertLess(worst, 1e-25)

    def test_ujsum_against_mpmath_leibniz(self):
        import mpmath as mp
        mp.mp.dps = 50
        fam, _, _, _ = instrument.load_owner()
        N = 6
        A = instrument.A_polys(N + 1)
        yv = 1.234
        worst = 0.0
        for (R0, th) in fam[:5]:
            R = mp.mpf(repr(R0))
            u = mp.mpf(repr(yv)) / R
            s = 1 - u * u
            lam = mp.mpf("0.5") + 1j * mp.mpf(repr(th))
            inner = mp.mpc(0)
            for j in range(N + 1):
                aj = sum(mp.mpf(ck) * u ** k for k, ck in enumerate(A[j]))
                inner += mp.binomial(N, j) * (R * lam) ** (N - j) * aj \
                    * s ** (2 * (N - j))
            ref = mp.e ** (lam * yv) * mp.e ** (-instrument.K / s) * inner \
                / (s ** (2 * N) * R ** N)
            d = instrument.family_cell_arrays_u(R0, th, N, A,
                                                np.array([yv - 1e-6]),
                                                np.array([yv + 1e-6]),
                                                instrument.KAPPA)
            worst = max(worst, float(abs(d["t_m"][0] - ref) / abs(ref)))
        self.assertLess(worst, 1e-9)

    def test_ode_derivative_identity(self):
        import mpmath as mp
        mp.mp.dps = 40
        A = instrument.A_polys(8)
        worst = 0.0
        for j in (1, 3, 5):
            u0 = mp.mpf("0.37")
            hh = mp.mpf("1e-6")
            s0 = 1 - u0 * u0
            a0 = sum(mp.mpf(ck) * u0 ** k for k, ck in enumerate(A[j]))
            a1 = sum(mp.mpf(ck) * u0 ** k for k, ck in enumerate(A[j + 1]))
            am = sum(mp.mpf(ck) * (u0 - hh) ** k for k, ck in enumerate(A[j]))
            ap = sum(mp.mpf(ck) * (u0 + hh) ** k for k, ck in enumerate(A[j]))
            fd = (ap - am) / (2 * hh)
            ident = (a1 - 2 * u0 * (2 * j * s0 - instrument.K) * a0) / s0 ** 2
            worst = max(worst, float(abs(fd - ident) / abs(ident)))
        self.assertLess(worst, 1e-5)

    def test_Sfun_is_a_true_cell_sup(self):
        import mpmath as mp
        mp.mp.dps = 40
        for (lo, hi) in ((0.0, 1.0), (0.05, 0.6), (0.3, 0.9), (0.7, 1.0)):
            for m in (0, 1, 2, 5, 11, 41):
                bound = float(instrument.Sfun(m, np.array([lo]), np.array([hi]))[0])
                grid = np.linspace(lo + 1e-9, hi - 1e-9, 4001)
                sup = float(np.max(np.exp(-instrument.K / grid
                                          - m * np.log(grid))))
                self.assertGreaterEqual(bound, sup * (1 - 1e-12))
                self.assertLessEqual(bound, sup * 1e6 + 1e-300)

    def test_ub_ge_lb_at_small_order(self):
        fam, base, corr, _ = instrument.load_owner()
        Ns = 12
        A = instrument.A_polys(Ns + 1)
        ylo, yhi, _ = instrument.master_grid(fam, 512)
        for vec in (base, corr):
            ub, lb, _ = instrument.ub_on_cells(fam, vec, Ns, A, ylo, yhi,
                                               instrument.KAPPA)
            self.assertTrue(np.all(np.isfinite(ub)))
            self.assertTrue(np.all(ub >= lb * (1 - 1e-12)))

    def test_provenance(self):
        prov = self.art["provenance"]
        self.assertEqual(prov["script"], "scripts/routea_hgap_tail_sharp_2306.py")
        self.assertTrue((ROOT / prov["script"]).is_file())
        self.assertTrue((ROOT / prov["owner"]).is_file())
        self.assertTrue((ROOT / prov["predecessor"]).is_file())


if __name__ == "__main__":
    unittest.main()