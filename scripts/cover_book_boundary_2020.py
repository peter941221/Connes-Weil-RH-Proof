#!/usr/bin/env python3
"""Record 2020 desk, labeled post-hoc diagnostic: the visible book is an exact
function of the scale coordinate.

The record-1998/2016 gate anatomy makes the visible prime book explicit:
`gate_entries` (fourpoint_owner_density_1959.py:386) sums over
`prime_powers_up_to(exp(support_radius))` (line 403), and the row builder sets
`support_radius = max(a for a, _ in fam) * (n + 2)` (lines 618/733) with n = 0
in the committed runs.  Every family width is `scale * pool[idx]`
(fourpoint_rh_reach_probe_1983.py:118), so the support radius - and hence the
visible prime-power set - is an exact function of (layer, height, scale).

This script recomputes that function on the committed nodes and compares it
with the measured `n_primes` of the committed record-2012 rows.  No
measurement: the comparison is a reproducibility check on committed JSONs
(record-1998 section 2 F-c pattern), and its output feeds the record-2020
book-boundary section.
"""

import json
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import fourpoint_owner_density_1959 as r59  # noqa: E402
import fourpoint_rh_reach_probe_1983 as r83  # noqa: E402
import routea_opposite_gates_height_1994 as r94  # noqa: E402

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ROWS = os.path.join(REPO, "results", "2012_cover_scan_rows_width.json")
OUT = os.path.join(REPO, "results", "2020_book_boundary.json")

DELTA = 0.10
SCALES = (0.80, 0.90, 1.00)


def main():
    with open(ROWS, encoding="utf-8") as stream:
        rows = json.load(stream)["rows"]
    measured = {}
    for row in rows:
        if abs(row["delta"] - DELTA) > 1e-9:
            continue
        key = (row["layer"], row["gamma"], round(row["scale"], 6))
        measured[key] = row["n_primes"]
    # NOTE: the physics must see the RAW gamma - family_for_g keys the main
    # group on abs(imag - g_main) < 1e-9, so a 6-decimal rounded gamma drops
    # the main node into the kill pool and shifts every width (caught in the
    # first probe run).  Only the measurement lookup key is rounded.
    slots = sorted(set((row["layer"], row["gamma"]) for row in rows
                       if abs(row["delta"] - DELTA) < 1e-9))

    out = {}
    print("slot                     scale  max_width  radius   exp(radius)  "
          "np_pred  np_measured  match")
    for layer, gk in slots:
        rho = (0.5 + DELTA) + 1j * gk
        if layer == "committed":
            nodes, _ = r83.owner_nodes_g(rho, gk)
            fam_fn = r83.family_for_g
        else:
            nodes, _ = r94.owner_nodes_ext(rho, gk)
            fam_fn = r94.family_for_ext
        for scale in SCALES:
            fam = fam_fn(nodes, scale, gk)
            max_width = max(a for a, _ in fam)
            radius = max_width * 2.0
            xmax = math.exp(radius)
            np_pred = len(r59.rig.prime_powers_up_to(xmax))
            np_meas = measured.get((layer, gk, scale))
            entry = {"layer": layer, "gamma": gk, "scale": scale,
                     "max_width": max_width, "support_radius": radius,
                     "xmax": xmax, "np_pred": np_pred, "np_measured": np_meas,
                     "match": bool(np_meas == np_pred)}
            out["%s:%.6f:%.2f" % (layer, gk, scale)] = entry
            print("%-24s %.2f  %9.5f  %6.4f  %11.3f  %7d  %11s  %s"
                  % ("%s:%.6f" % (layer, gk), scale, max_width, radius, xmax,
                     np_pred, np_meas, "OK" if entry["match"] else "MISMATCH"))

    # Book-step spacing at the window edge: the density of prime powers near
    # xmax(scale = 1.00) sets the scale-resolution at which the book is
    # constant between steps.
    steps = {}
    for layer, gk in slots:
        rho = (0.5 + DELTA) + 1j * gk
        if layer == "committed":
            nodes, _ = r83.owner_nodes_g(rho, gk)
            fam_fn = r83.family_for_g
        else:
            nodes, _ = r94.owner_nodes_ext(rho, gk)
            fam_fn = r94.family_for_ext
        fam = fam_fn(nodes, 1.00, gk)
        radius = 2.0 * max(a for a, _ in fam)
        xw = math.exp(radius)
        x0 = math.exp(2.0 * 0.995 * max(a for a, _ in fam_fn(nodes, 0.995, gk)))
        # local prime-power density in [x0, xw]: count near the edge
        near = [n for n, _ in r59.rig.prime_powers_up_to(xw)]
        count_edge = sum(1 for n in near if n > x0)
        dlog = 2.0 * 0.005 * max(a for a, _ in fam_fn(nodes, 1.00, gk))
        step_spacing = dlog / count_edge if count_edge else None
        steps["%s:%.6f" % (layer, gk)] = {
            "xmax": xw, "prime_powers_in_last_half_percent": count_edge,
            "book_step_spacing_in_scale": step_spacing}
        print("step spacing %-24s: %d prime powers per 0.005 scale near the "
              "edge -> spacing ~ %s"
              % ("%s:%.6f" % (layer, gk), count_edge,
                 ("%.4f" % step_spacing) if step_spacing else "n/a"))

    with open(OUT, "w", encoding="utf-8") as stream:
        json.dump({"record": "2020", "delta": DELTA, "scales": list(SCALES),
                   "cells": out, "book_step_spacing": steps}, stream,
                  indent=2)
        stream.write("\n")
    print("results -> %s" % OUT)


if __name__ == "__main__":
    main()