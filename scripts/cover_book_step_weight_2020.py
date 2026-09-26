#!/usr/bin/env python3
"""Record 2020 desk, labeled post-hoc diagnostic: the weight of one book step.

The route-B prime channel of `gate_entries` (fourpoint_owner_density_1959.py,
lines 442-447) is a sum of per-prime-power terms over the visible book:

    Kp(xi)   = sum_n 2 * Lambda(n)/sqrt(n) * cos(2 pi xi log n)
    prime[f] = integral Kp * f dxi,   f = W, P*W, P*P*W

so when the scale s crosses a book boundary (a new prime power n enters the
set prime_powers_up_to(exp(support_radius))), C jumps by exactly

    delta_n = 2 * Lambda(n)/sqrt(n) * What(log n),

with What the cosine transform of W.  This script computes the per-term
weights on two committed cells - one committed-layer cell (coarse book, step
spacing ~2e-3 in scale) and one EXT cell (fine book, spacing ~1e-4) - and
reports each term against |C| and against the number of book steps inside one
0.01 scale cell.  No new cell is measured: the row machinery is rebuilt for
the same committed (layer, gamma, delta, scale) and the committed C/D values
are quoted alongside as a route-level reproducibility check (route B vs the
certified-route value of the committed row; the difference should sit at the
route spread).

Writes results/2020_book_step_weight.json.
"""

import json
import math
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import fourpoint_owner_density_1959 as r59  # noqa: E402
import fourpoint_owner_completion_1980 as r80  # noqa: E402
import fourpoint_rh_reach_probe_1983 as r83  # noqa: E402
import routea_opposite_gates_height_1994 as r94  # noqa: E402

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ROWS = os.path.join(REPO, "results", "2012_scan_rows_width.json")
ROWS_WIDTH = os.path.join(REPO, "results", "2012_cover_scan_rows_width.json")
OUT = os.path.join(REPO, "results", "2020_book_step_weight.json")

K = 30.0
XI_MAX = 40.0
DXI = 0.004
DELTA = 0.10
CELLS = [
    ("committed", r80.GAMMA1, 0.88),
    ("ext", r94.G7, 0.92),
]


def cell_data(layer, gk, scale):
    rho = (0.5 + DELTA) + 1j * gk
    if layer == "committed":
        nodes, values = r83.owner_nodes_g(rho, gk)
        fam = r83.family_for_g(nodes, scale, gk)
    else:
        nodes, values = r94.owner_nodes_ext(rho, gk)
        fam = r94.family_for_ext(nodes, scale, gk)
    XW = r80.family_quad(fam, K)
    A = r80.amplitudes(nodes, values, fam, K, XW)
    nxi = int(round(2.0 * XI_MAX / DXI)) + 1
    xi = np.linspace(-XI_MAX, XI_MAX, nxi)
    W, _Lb, _Lc, _r = r80.owner_density(nodes, fam, K, 0, xi, XW,
                                        (A[0], A[1]))
    P = np.real(r59.P_from_nodes(xi, r80.counterpart_nodes(rho)))
    support_radius = max(a for a, _ in fam) * 2.0
    return xi, W, P, support_radius


def main():
    with open(ROWS_WIDTH, encoding="utf-8") as stream:
        rows = json.load(stream)["rows"]
    committed = {}
    for row in rows:
        if abs(row["delta"] - DELTA) < 1e-9:
            committed[(row["layer"], row["gamma"], round(row["scale"], 6))] = row

    xi = None
    out = {}
    for layer, gk, scale in CELLS:
        xi, W, P, radius = cell_data(layer, gk, scale)
        dxi = float(xi[1] - xi[0])
        sig = r59.rig.sigma_vec(2.0 * np.pi * xi)
        pset = r59.rig.prime_powers_up_to(math.exp(radius))
        arch = [float(np.trapezoid(sig * f, xi))
                for f in (W, P * W, P * P * W)]
        # route B, verbatim shape, plus the per-term vector for f = W
        Kp = np.zeros_like(sig)
        terms = []
        for nn, lam in pset:
            cosv = np.cos(2.0 * np.pi * xi * math.log(nn))
            Kp = Kp + 2.0 * lam * math.sqrt(1.0 / nn) * cosv
            terms.append(2.0 * lam * math.sqrt(1.0 / nn)
                         * float(np.trapezoid(cosv * W, xi)))
        prime = [float(np.trapezoid(Kp * f, xi))
                 for f in (W, P * W, P * P * W)]
        C_B = arch[0] + prime[0]
        D_B = arch[2] + prime[2]
        term_abs = np.abs(np.array(terms, dtype=float))
        term_rel = term_abs / abs(C_B) if C_B else np.full_like(term_abs, np.inf)
        row = committed.get((layer, gk, scale))
        # book steps inside one 0.01 scale cell at this scale: the radius is
        # linear in s (radius = max_width * 2 * s), so with w0 = radius / s
        # the book boundary at scale s' is exp(w0 * s')
        w0 = radius / scale
        x_lo = math.exp(w0 * (scale - 0.005))
        x_hi = math.exp(w0 * (scale + 0.005))
        step_ns = [(nn, lam) for nn, lam in r59.rig.prime_powers_up_to(x_hi)
                   if nn > x_lo]
        steps = len(step_ns)
        # the decisive statistic: the terms that ENTER while the scale crosses
        # one 0.01 cell are the largest primes in the book (near the boundary),
        # not the book's biggest terms (the low primes, which never step)
        step_abs = np.abs(np.array(
            [2.0 * lam * math.sqrt(1.0 / nn)
             * float(np.trapezoid(np.cos(2.0 * np.pi * xi * math.log(nn)) * W,
                                  xi))
             for nn, lam in step_ns], dtype=float))
        entry = {
            "layer": layer, "gamma": gk, "scale": scale, "dxi": dxi,
            "support_radius": radius, "n_primes": len(pset),
            "arch": arch, "prime_B": prime,
            "C_routeB": C_B, "D_routeB": D_B,
            "C_committed": row["C"] if row else None,
            "D_committed": row["D"] if row else None,
            "term_max_abs": float(term_abs.max()),
            "term_median_abs": float(np.median(term_abs)),
            "term_max_over_C": float(term_rel.max()),
            "term_median_over_C": float(np.median(term_rel)),
            "steps_per_001_scale_cell": steps,
            "step_terms_max_over_C": (float(step_abs.max() / abs(C_B))
                                      if steps else 0.0),
            "step_terms_sum_over_C": (float(step_abs.sum() / abs(C_B))
                                      if steps else 0.0),
            "prime_channel_over_C": abs(prime[0]) / abs(C_B) if C_B else None,
        }
        out["%s:%.6f:%.2f" % (layer, gk, scale)] = entry
        print("cell %s:%.6f sc %.2f" % (layer, gk, scale))
        print("  n_primes %d, support radius %.4f, steps inside one 0.01 "
              "cell: %d" % (len(pset), radius, steps))
        print("  C (route B) %+.6e   committed C %s  (D %+.3e / %s)"
              % (C_B, ("%+.6e" % row["C"]) if row else "n/a", D_B,
                 ("%+.3e" % row["D"]) if row else "n/a"))
        print("  prime channel |prime|/|C| = %.3f" % (abs(prime[0]) / abs(C_B)))
        print("  all-term |max|/|C| = %.4e   median/|C| = %.4e"
              % (float(term_rel.max()), float(np.median(term_rel))))
        print("  STEPPING terms (entering inside one 0.01 cell): max/|C| = "
              "%.4e  sum/|C| = %.4e"
              % (float(step_abs.max() / abs(C_B)) if steps else 0.0,
                 float(step_abs.sum() / abs(C_B)) if steps else 0.0))

    with open(OUT, "w", encoding="utf-8") as stream:
        json.dump({"record": "2020", "delta": DELTA, "cells": out}, stream,
                  indent=2)
        stream.write("\n")
    print("results -> %s" % OUT)


if __name__ == "__main__":
    main()