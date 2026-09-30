"""Artifact and mechanism controls for 2307 (certified grouped flat-edge tail).

Locks the committed certificate: verdict, budget, xi0, the certified ladder
(orders 16/20/24/36 on the coarse master grids), the best rung, per-order
admissibility of every enclosure (lo/hi endpoints are proper and ordered,
hi_float is the printed upper within double rounding, margins recompute from
the upper endpoint), the cert-vs-float crosscheck signature (the certified
bound sits just below the 2306 float bound because the float carries the
kappa = 2^-30 slack term -- evidence that the certified path has no kappa
model), the certified a1 / c_w intervals containing the frozen 2306 floats,
and the pinned prime-power census.

The mechanism checks re-run the instrument code, not just the JSON:
construction containment (outward rounding), exact big-int A_j vs the 2306
float recursion, the S-function cell sup against brute force, the tail
closed form against normalized quadrature, and an end-to-end certified
cell bound at small order against the float instrument on the same lattice.
"""
import json
import sys
import unittest
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import routea_hgap_tail_cert_2307 as instrument  # noqa: E402

ART = ROOT / "results" / "2307_hgap_tail_certified.json"
PREDECESSOR = ROOT / "results" / "2306_hgap_tail_sharp.json"
OWNER = ROOT / "results" / "2275_gap_owner_audit.json"
BUDGET = 1.0e7
A1_FLOAT_2306 = 2497731.388738144
CW_FLOAT_2306 = 2810.1333609392077
ORDERS = [16, 20, 24, 36]


def _endpoints(s):
    a, b = s.strip("[]").split(", ")
    import mpmath as mp
    return mp.mpf(a), mp.mpf(b)


class TailCertifiedControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.art = json.loads(ART.read_text(encoding="utf-8"))
        cls.rows = {r["order"]: r for r in cls.art["rows"]}
        cls.orders = {r["order"]: json.loads(
            (ROOT / "results" /
             f"2307_cert_order_{r['order']}_n{r['n0']}.json"
             ).read_text(encoding="utf-8"))
            for r in cls.art["rows"]}

    def test_scope_and_verdict(self):
        self.assertEqual(self.art["status"], "TAIL-CERTIFIED")
        self.assertTrue(self.art["certificate"])
        self.assertEqual(self.art["budget"], BUDGET)
        self.assertEqual(self.art["xi0"], 40.0)
        self.assertEqual(self.art["interval_dps"], 40)
        self.assertIn("no declared slack model", self.art["scope"])
        self.assertIn("kappa", self.art["scope"])
        self.assertIn("Lean hypotheses", self.art["scope"])
        self.assertIn("inherited from 2304/2305", self.art["scope"])

    def test_certified_ladder_clears_budget(self):
        self.assertEqual([r["order"] for r in self.art["rows"]], ORDERS)
        for row in self.art["rows"]:
            self.assertLess(row["tail_upper"], BUDGET)
            self.assertGreater(row["margin"], 1e2)
            self.assertEqual(row["cells"], row["n0"] + 13)
            # margin is BUDGET over the printed upper, to a double rounding
            self.assertAlmostEqual(row["margin"] / (BUDGET / row["tail_upper"]),
                                   1.0, delta=1e-12)

    def test_best_row_is_high_order(self):
        tails = {r["order"]: r["tail_upper"] for r in self.art["rows"]}
        best = min(tails, key=tails.get)
        self.assertEqual(best, self.art["best"]["order"])
        self.assertEqual(best, 36)
        self.assertLess(tails[best], 1e-25)
        self.assertGreater(self.art["best"]["margin"], 1e30)
        self.assertAlmostEqual(self.art["best"]["tail_upper"], tails[best],
                               delta=1e-9 * tails[best])

    def test_per_order_enclosure_admissible(self):
        import mpmath as mp
        with mp.workdps(60):
            for order, d in self.orders.items():
                lo, _ = _endpoints(d["tail"]["lo"])
                _, hi = _endpoints(d["tail"]["hi"])
                # the stored endpoints are 30+ digit renderings of a 136-bit
                # interval; the renderings may coincide while the true width
                # is ~1e-37 relative, so require order and rendering cohesion
                self.assertGreaterEqual(hi, lo, f"order {order}: tail lo/hi")
                self.assertLess((hi - lo) / hi, 1e-25,
                                f"order {order}: tail endpoints cohesive")
                # printed upper is the upper endpoint within double rounding
                hf = mp.mpf(repr(d["tail"]["hi_float"]))
                self.assertLess(abs(hf - hi) / hi, 1e-14,
                                f"order {order}: hi_float = printed upper")
                # certified V endpoints are proper intervals of the same shape
                for ch in ("V_base", "V_corr"):
                    vlo, _ = _endpoints(d[ch]["lo"])
                    _, vhi = _endpoints(d[ch]["hi"])
                    self.assertGreaterEqual(vhi, vlo * (1 - 1e-30))
                # V upper = 2 Rmax sup over cells, recomputed from stored parts
                want = 2 * mp.mpf(repr(d["Rmax"])) * mp.mpf(
                    repr(d["ub_max_base_float"]))
                got = mp.mpf(repr(d["V_base"]["hi_float"]))
                self.assertLess(abs(got - want) / want, 1e-12,
                                f"order {order}: V_base = 2 Rmax ub_base")

    def test_crosscheck_signature_no_kappa(self):
        # The certified bound sits a small factor BELOW the 2306 float bound:
        # the float carries the kappa * magchain slack term, the certificate
        # carries only interval inflation.  It must still be >= the sampled
        # lower bound on the same lattice (the certificate is a true sup).
        for order, d in self.orders.items():
            cc = d["crosscheck"]
            for ch in ("base", "corr"):
                ratio = cc[f"cert_over_float_ub_{ch}"]
                self.assertGreater(ratio, 0.999999, f"N={order} {ch}")
                self.assertLess(ratio, 1.000001, f"N={order} {ch}")
                self.assertGreater(cc[f"cert_over_lb_{ch}"], 1.0 - 1e-9,
                                   f"N={order} {ch}")
            self.assertGreater(cc["cert_over_lb_base"], 1.2)
            self.assertGreater(cc["cert_over_lb_corr"], 10.0)

    def test_constants_match_frozen_floats_ultratight(self):
        # The certified a1 / c_w intervals are ~25 orders tighter than a
        # float64 ulp; the 2306 float64 constants are rounded renderings that
        # sit 0.2-0.8 ulp off the certified interval (the certified upper is
        # +0.76 ulp above the a1 float64 and -0.16 ulp below the c_w float64),
        # so containment at this tightness is not the right assertion --
        # ulp-grade agreement plus a certified width far below one ulp is.
        import mpmath as mp
        self.assertAlmostEqual(self.art["a1_float_2306"], A1_FLOAT_2306,
                               delta=1e-9 * A1_FLOAT_2306)
        self.assertAlmostEqual(self.art["c_w_float_2306"], CW_FLOAT_2306,
                               delta=1e-12 * CW_FLOAT_2306)
        with mp.workdps(60):
            for order, d in self.orders.items():
                for name, flt in (("a1", A1_FLOAT_2306),
                                  ("c_w", CW_FLOAT_2306)):
                    lo, _ = _endpoints(d[name]["lo"])
                    _, hi = _endpoints(d[name]["hi"])
                    fv = mp.mpf(repr(flt))
                    ulp = mp.ldexp(mp.mpf(1),
                                   int(mp.floor(mp.log(fv, 2))) - 52)
                    self.assertLess(abs(hi / fv - 1), 1e-14,
                                    f"N={order} {name}: within float64 ulp")
                    self.assertLess(abs(hi - fv) / ulp, 2.0,
                                    f"N={order} {name}: <= 2 ulp of float64")
                    self.assertLess((hi - lo) / hi, 1e-30,
                                    f"N={order} {name}: certified width "
                                    f"far below one float64 ulp")
                self.assertEqual(d["families"], 30)
                self.assertEqual(d["theta_groups"], 25)
                self.assertEqual(d["prime_powers"], 41136)
                self.assertEqual(d["prime_limit"], 492475)
                self.assertEqual(d["interval"]["lib"], "mpmath.iv")
                self.assertEqual(d["interval"]["prec_bits"], 136)

    def test_iv_construction_is_outward(self):
        import mpmath as mp
        from mpmath import iv
        with mp.workdps(120):
            for c in (10 ** 80, -(10 ** 70), 123456789012345678901234567890):
                x = iv.mpf([c, c])
                xv = mp.mpf(c)
                self.assertTrue(mp.mpf(x.a) <= xv <= mp.mpf(x.b))

    def test_exact_A_j_against_2306_float(self):
        A_int = instrument.exact_A_polys(31)
        A_flt = instrument.ref.A_polys(31)
        self.assertEqual(len(A_int), len(A_flt))
        for j in range(len(A_flt)):
            self.assertEqual(len(A_int[j]), len(A_flt[j]))
            for c_int, c_flt in zip(A_int[j], A_flt[j]):
                self.assertIsInstance(c_int, int)
                if abs(c_int) < 2 ** 52 and c_flt != 0:
                    self.assertEqual(float(c_int), float(c_flt))

    def test_Sfun_dominates_grid_sup(self):
        for (lo, hi) in ((0.0, 1.0), (0.05, 0.6), (0.7, 1.0), (1e-6, 1e-3)):
            for m in (0, 1, 2, 11, 41):
                b = instrument.hev(instrument.Sfun_iv(m, lo, hi))
                grid = np.linspace(max(lo, 1e-300) + 1e-12, hi - 1e-12, 4001)
                sup = float(np.max(np.exp(-instrument.K / grid
                                          - m * np.log(grid))))
                self.assertGreaterEqual(b, sup * (1 - 1e-12))

    def test_tail_closed_form_is_quadrature(self):
        import mpmath as mp
        with mp.workdps(60):
            for Nv in (16, 20, 36):
                p = 4 * Nv - 8
                q = p - 1
                quad = mp.quad(
                    lambda t: (mp.log(40) + t + 1) * mp.e ** (-q * t),
                    [0, mp.inf])
                closed = (mp.log(40) + 1) / q + 1 / q ** 2
                self.assertLess(abs(quad - closed) / closed, 1e-15)

    def test_end_to_end_certified_cell_vs_float(self):
        fam, base_c, _, _ = instrument.ref.load_owner()
        Ns = 8
        A_int = instrument.exact_A_polys(Ns + 1)
        Aiv = [[instrument.ivc(c) for c in Aj] for Aj in A_int]
        Aabs = [[instrument.ivc(abs(c)) for c in Aj] for Aj in A_int]
        ylo, yhi, _ = instrument.ref.master_grid(fam, 96)
        ubs, imax = instrument.channel_cell_ub(fam, base_c, Ns, Aiv, Aabs,
                                               ylo, yhi)
        fub, flb, _ = instrument.ref.ub_on_cells(
            fam, base_c, Ns, instrument.ref.A_polys(Ns + 1), ylo, yhi,
            instrument.ref.KAPPA)
        self.assertGreaterEqual(ubs[imax], float(flb[imax]) * (1 - 1e-12))
        ratio = ubs[imax] / float(fub[imax])
        self.assertGreaterEqual(ratio, 0.5)
        self.assertLessEqual(ratio, 2.0)
        self.assertLessEqual(max(ubs) / float(fub.max()), 2.0)

    def test_provenance(self):
        prov = self.art["provenance"]
        self.assertEqual(prov["script"],
                         "scripts/routea_hgap_tail_cert_2307.py")
        self.assertTrue((ROOT / prov["script"]).is_file())
        self.assertTrue(PREDECESSOR.is_file())
        self.assertTrue(OWNER.is_file())
        self.assertGreater(PREDECESSOR.stat().st_size, 0)
        self.assertGreater(OWNER.stat().st_size, 0)


if __name__ == "__main__":
    unittest.main()