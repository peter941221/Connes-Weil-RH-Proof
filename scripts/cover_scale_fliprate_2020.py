#!/usr/bin/env python3
"""Record 2020 desk, labeled post-hoc diagnostic: the scale flip rate of C.

Why: the direction-C currency question asks whether the healthy set has
*interval* currency along the scale coordinate.  The measured comb (record
2016) is a 0.01-scale grid; whether the sign of C between grid points is
smooth or noise decides whether a healthy window is a real object or a run in
a random sequence.  This is a pure post-hoc reading of committed rows (no
measurement): for every pair of certified cells (face != INSTRUMENT) at
scale distance h, count how often sign(C) (and the healthy indicator
C>0 & D<0 & det<0, face WIRE1) differs between the two ends.

Reading rule (fixed here, applied to the pooled numbers):

    ratio = R(h = 0.02) / R(h = 0.01), same 21-point grid, certified pairs

    ratio >= 1.4   COMB-SMOOTH        flip rate grows with distance: signs are
                                      correlated over >= 0.02 and the comb has
                                      real band structure
    0.7 <= ratio < 1.4   COMB-WHITE   flip rate flat in h: signs at 0.01 apart
                                      are already independent; the grid is a
                                      fair random sampler of the healthy set
                                      (so the measured healthy fraction is an
                                      unbiased estimate of the healthy measure)
    ratio < 0.7    COMB-ALTERNATING   anti-correlated: preferred period near
                                      0.02

The independence reference is 2*mu*(1-mu) with mu the certified fraction of
the same indicator; a flip rate within 3 sigma of it (sigma =
sqrt(p(1-p)/n)) is called AT-INDEPENDENCE for that indicator.

Cross-instrument check: the five-point floor grid (scales 0.86..0.94, step
0.02, same delta = 0.10) gives an independent R(0.02) reading on disjoint
pairs.

Writes results/2020_flip_rate.json.
"""

import json
import math
import os
from collections import defaultdict

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
WIDTH_ROWS = os.path.join(REPO, "results", "2012_cover_scan_rows_width.json")
FLOOR_ROWS = os.path.join(REPO, "results", "2012_cover_scan_rows_floor.json")
OUT = os.path.join(REPO, "results", "2020_flip_rate.json")

DELTA = 0.10
GRID_STEP = 0.01
MAX_STRIDE = 4


def is_healthy(row):
    return row.get("face") == "WIRE1"


def certified(row):
    return row.get("face") != "INSTRUMENT"


def load_slots(path, delta):
    with open(path, encoding="utf-8") as stream:
        rows = json.load(stream)["rows"]
    slots = defaultdict(dict)
    for row in rows:
        if abs(row["delta"] - delta) > 1e-9:
            continue
        if certified(row):
            slots[(row["layer"], row["gamma"])][round(row["scale"], 6)] = row
    return slots


def pair_stats(slot, stride, step):
    scales = sorted(slot)
    n = 0
    c_flip = 0
    h_flip = 0
    for i in range(len(scales) - stride):
        a = slot[scales[i]]
        b = slot[scales[i + stride]]
        if abs((b["scale"] - a["scale"]) - stride * step) > 1e-6:
            continue
        n += 1
        if (a["C"] > 0) != (b["C"] > 0):
            c_flip += 1
        if is_healthy(a) != is_healthy(b):
            h_flip += 1
    return n, c_flip, h_flip


def rate(f, n):
    return (f / n) if n else None


def indep_ref(mu):
    return 2.0 * mu * (1.0 - mu)


def classify(ratio_c, ratio_h):
    if ratio_c is None:
        return None
    if ratio_c >= 1.4:
        return "COMB-SMOOTH"
    if ratio_c < 0.7:
        return "COMB-ALTERNATING"
    if ratio_h is not None and ratio_h >= 1.4:
        return "COMB-SMOOTH"
    if ratio_h is not None and ratio_h < 0.7:
        return "COMB-ALTERNATING"
    return "COMB-WHITE"


def sigma(p, n):
    return math.sqrt(p * (1.0 - p) / n) if n else 0.0


def main():
    slots = load_slots(WIDTH_ROWS, DELTA)
    floor = load_slots(FLOOR_ROWS, DELTA)

    per_slot = {}
    pooled = {stride: {"n": 0, "c_flip": 0, "h_flip": 0,
                       "c_rate": 0.0, "h_rate": 0.0}
              for stride in range(1, MAX_STRIDE + 1)}
    pooled_cells = 0
    pooled_hosts = 0
    for key in sorted(slots):
        slot = slots[key]
        entry = {"n_cells": len(slot),
                 "mu_healthy": sum(1 for s in slot if is_healthy(slot[s]))
                 / len(slot),
                 "mu_c_pos": sum(1 for s in slot if slot[s]["C"] > 0)
                 / len(slot),
                 "by_stride": {}}
        for stride in range(1, MAX_STRIDE + 1):
            n, c_flip, h_flip = pair_stats(slot, stride, GRID_STEP)
            entry["by_stride"]["h=%.2f" % (stride * GRID_STEP)] = {
                "n_pairs": n,
                "c_flip": c_flip, "c_rate": rate(c_flip, n),
                "h_flip": h_flip, "h_rate": rate(h_flip, n)}
            pooled[stride]["n"] += n
            pooled[stride]["c_flip"] += c_flip
            pooled[stride]["h_flip"] += h_flip
        pooled_cells += len(slot)
        pooled_hosts += sum(1 for s in slot if is_healthy(slot[s]))
        per_slot["%s:%.6f" % key] = entry

    for stride in pooled:
        blob = pooled[stride]
        blob["c_rate"] = rate(blob["c_flip"], blob["n"])
        blob["h_rate"] = rate(blob["h_flip"], blob["n"])

    mu_h = pooled_hosts / pooled_cells
    ref_h = indep_ref(mu_h)
    ref_c = indep_ref(sum(entry["mu_c_pos"] for entry in per_slot.values())
                      / len(per_slot))
    ratio_c = (pooled[2]["c_rate"] / pooled[1]["c_rate"])
    ratio_h = (pooled[2]["h_rate"] / pooled[1]["h_rate"])
    verdict = classify(ratio_c, ratio_h)

    # cross-instrument: floor grid, h = 0.02 on disjoint pairs
    fn = fc = fh = 0
    for key in sorted(floor):
        n, c_flip, h_flip = pair_stats(floor[key], 1, 0.02)
        fn += n
        fc += c_flip
        fh += h_flip
    floor_check = {"n_pairs": fn, "c_rate": rate(fc, fn), "h_rate": rate(fh, fn)}

    print("pooled certified cells %d, healthy fraction mu = %.4f "
          "(H = 1/mu = %.2f)" % (pooled_cells, mu_h, 1.0 / mu_h))
    for stride in sorted(pooled):
        blob = pooled[stride]
        print("  h=%.2f: C flip %d/%d = %.3f   healthy flip %d/%d = %.3f"
              % (stride * GRID_STEP, blob["c_flip"], blob["n"], blob["c_rate"],
                 blob["h_flip"], blob["n"], blob["h_rate"]))
    print("independence refs: C %.3f, healthy %.3f (3-sigma bands %.3f..%.3f)"
          % (ref_c, ref_h, ref_h - 3 * sigma(ref_h, pooled[1]["n"]),
             ref_h + 3 * sigma(ref_h, pooled[1]["n"])))
    print("floor-grid cross-check h=0.02 (%d disjoint pairs): C %.3f, "
          "healthy %.3f" % (fn, floor_check["c_rate"], floor_check["h_rate"]))
    print("ratio R(0.02)/R(0.01): C %.3f, healthy %.3f" % (ratio_c, ratio_h))
    print("VERDICT: %s" % verdict)
    for name, entry in per_slot.items():
        b = entry["by_stride"]
        rc = (b["h=0.02"]["c_rate"] / b["h=0.01"]["c_rate"]
              if b["h=0.01"]["c_rate"] else None)
        rh = (b["h=0.02"]["h_rate"] / b["h=0.01"]["h_rate"]
              if b["h=0.01"]["h_rate"] else None)
        print("  %-22s C %.2f H %.2f ratio_C %s ratio_H %s -> %s"
              % (name, b["h=0.01"]["c_rate"], b["h=0.01"]["h_rate"],
                 ("%.2f" % rc) if rc is not None else "n/a",
                 ("%.2f" % rh) if rh is not None else "n/a",
                 classify(rc, rh)))

    with open(OUT, "w", encoding="utf-8") as stream:
        json.dump({"record": "2020", "kind": "scale flip-rate (post-hoc)",
                   "delta": DELTA, "grid_step": GRID_STEP,
                   "width_rows": "results/2012_cover_scan_rows_width.json",
                   "floor_rows": "results/2012_cover_scan_rows_floor.json",
                   "pooled": {"cells": pooled_cells, "mu_healthy": mu_h,
                              "H": 1.0 / mu_h, "by_stride": pooled,
                              "ref_c": ref_c, "ref_h": ref_h,
                              "ratio_c": ratio_c, "ratio_h": ratio_h},
                   "floor_grid_cross_check": floor_check,
                   "verdict": verdict, "per_slot": per_slot}, stream,
                  indent=2)
        stream.write("\n")
    print("results -> %s" % OUT)


if __name__ == "__main__":
    main()