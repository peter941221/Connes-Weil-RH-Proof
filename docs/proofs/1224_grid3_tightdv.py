#!/usr/bin/env python3
"""Record 1224 sec.3g supplement: tight per-element 3-sigma propagation of
the row-volume statistic (MODEL, law 65).

The registered dv bound in sec.3f (sum_i 3*maxcol_sigma_i / ||row_i||) is
an ANGLE bound: it overestimates the volume change achievable within 3
sigma because (i) it uses the max sigma of each row for all three entries
and (ii) it ignores the direction leverage of the row cross product.  This
script recomputes the honest bound

  dv_tight = sum_i sum_j |n_j| * 3 sigma_ij / (||r_0.5|| ||r_1|| ||r_2||),
  n = r_1 x r_2 (any row's cross partners give the same |det| response;
  the bound is evaluated per row with that row's own normal partner).

For row i the volume responds to a perturbation delta_i as
  delta_v = |delta_i . (r_j x r_k)| / prod||r||,
so the per-element 3-sigma worst case uses the normal partner of THAT row.

Also reports: the lambda-increment table (sign flip diagnostic) and each
row's reconstruction residual from the other two rows, in sigma units.
"""
import json
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import importlib.util

_spec = importlib.util.spec_from_file_location(
    "dial_analysis_1224", os.path.join(HERE, "1224_dial_analysis.py"))
assert _spec is not None and _spec.loader is not None
ana = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ana)

SIGMA_FLOOR = 1e28
LAM = [0.5, 1.0, 2.0]
SCOL = ["S1", "S3", "S6"]
TAGS = {(0.5, "S1"): "L05_S2", (0.5, "S3"): "L05_S235",
        (0.5, "S6"): "L05_S23571113",
        (1.0, "S1"): "L10_S2", (1.0, "S3"): "L10_S235",
        (1.0, "S6"): "L10_S23571113",
        (2.0, "S1"): "L20_S2", (2.0, "S3"): "L20_S235",
        (2.0, "S6"): "L20_S23571113"}


def fp_sigma(tag):
    with open(os.path.join(HERE, f"1224_dial_{tag}.json")) as fh:
        d = json.load(fh)
    fit = ana.fit_fp(ana.fine_rows(d))
    sigma = max(fit["spread_rel"] * abs(fit["FP"]), SIGMA_FLOOR)
    return fit["FP"], sigma


def cross(a, b):
    return (a[1] * b[2] - a[2] * b[1],
            a[2] * b[0] - a[0] * b[2],
            a[0] * b[1] - a[1] * b[0])


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def norm(a):
    return math.sqrt(dot(a, a))


def main():
    fp, sg = {}, {}
    for k, tag in TAGS.items():
        fp[k], sg[k] = fp_sigma(tag)
    rows = [[fp[(l, s)] for s in SCOL] for l in LAM]
    sigs = [[sg[(l, s)] for s in SCOL] for l in LAM]
    nrm = [norm(r) for r in rows]
    prod = nrm[0] * nrm[1] * nrm[2]
    det = dot(rows[0], cross(rows[1], rows[2]))
    v = abs(det) / prod
    print("grid rows (e+32):")
    for i, l in enumerate(LAM):
        print("  lam=%.1f  %s   sigmas(e+30): %s" %
              (l, "  ".join("%9.4f" % (x / 1e32) for x in rows[i]),
               "  ".join("%6.2f" % (s / 1e30) for s in sigs[i])))
    print("v = %.4e   prod||r|| = %.4e" % (v, prod))

    # tight per-element 3-sigma bound, per row with that row's normal partner
    dv_tight = 0.0
    for i in range(3):
        j, k = (i + 1) % 3, (i + 2) % 3
        nrm_partner = cross(rows[j], rows[k])
        contrib = sum(abs(nrm_partner[t]) * 3.0 * sigs[i][t]
                      for t in range(3)) / prod
        print("  row lam=%.1f: |normal partner| = %.3e, dv contribution "
              "= %.3e" % (LAM[i], norm(nrm_partner), contrib))
        dv_tight += contrib
    print("dv_tight (per-element 3-sigma) = %.4e" % dv_tight)
    print("registered dv (sec.3f angle bound) = 9.873e-03")
    print("-> v %s dv_tight  =>  %s under the tight bound" %
          ("<=" if v <= dv_tight else ">",
           "RANK-2" if v <= dv_tight else "RANK-3"))

    # lambda-increment table (additive-class diagnostic)
    print("\nlambda increments FP(lam',S) - FP(1,S)  (e+32):")
    for i, l in ((0, 0.5), (2, 2.0)):
        inc = [(rows[i][t] - rows[1][t]) / 1e32 for t in range(3)]
        print("  lam=%.1f minus lam=1:  %s" %
              (l, "  ".join("%+9.4f" % x for x in inc)))

    # multiplicative ratios
    print("lambda ratios FP(lam,S)/FP(1,S):")
    for i, l in ((0, 0.5), (2, 2.0)):
        rat = [rows[i][t] / rows[1][t] for t in range(3)]
        print("  lam=%.1f / lam=1:      %s" %
              (l, "  ".join("%+9.4f" % x for x in rat)))

    # reconstruction of each row from the other two, residuals in sigma
    print("\nrow reconstruction from the other two rows (sigma units):")
    for i in range(3):
        j, k = (i + 1) % 3, (i + 2) % 3
        # solve a*r_j + b*r_k = r_i on the first two columns, test the third
        a11, a12 = rows[j][0], rows[k][0]
        a21, a22 = rows[j][1], rows[k][1]
        d = a11 * a22 - a12 * a21
        A = (rows[i][0] * a22 - a12 * rows[i][1]) / d
        Bc = (a11 * rows[i][1] - rows[i][0] * a21) / d
        pred3 = A * rows[j][2] + Bc * rows[k][2]
        res = (rows[i][2] - pred3) / sg[(LAM[i], SCOL[2])]
        print("  row lam=%.1f = %+.4f * r(%.1f) %+.4f * r(%.1f);  S6 "
              "predicted %.4e vs measured %.4e -> residual %+.1f sigma" %
              (LAM[i], A, LAM[j], Bc, LAM[k], pred3, rows[i][2], res))


if __name__ == "__main__":
    main()
