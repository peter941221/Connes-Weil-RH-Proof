#!/usr/bin/env python3
"""Record-2026 COVER refinement census: the registered cell lists for the
0.001-grid EXT refinement (U), the delta axis of the C sign STRING on the six
record-2024 slots (D), and the five-point string census (S).

Everything is GENERATED from the committed row artifacts, never typed: the
preload lists are read out of the artifacts and each block records how many
registered grid positions are new.  The rig re-checks the arithmetic in its
A0 census clause (the record-2019/2024 rule).

Artifacts read:
  results/2012_cover_scan_rows_floor.json  the six registered deltas, five
                                           point cells, all nine slots
  results/2024_ladder9_rows.json           the six P1 slots at delta 0.10,
                                           grids 0.005 / 0.002
  results/2021_scale_ladder_rows.json      the three C1 slots at delta 0.10

Writes results/2026_registered_cells.json.
"""

import json
import os
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(REPO, "scripts"))

import fourpoint_owner_completion_1980 as r80  # noqa: E402
import routea_opposite_gates_height_1994 as r94  # noqa: E402

RANGE = (0.86, 0.96)
DXI = 0.004
DELTAS = (0.02, 0.05, 0.10, 0.15, 0.20, 0.30)
FIVE_POINT = (0.86, 0.88, 0.90, 0.92, 0.94)

# the nine registered slots: committed gamma_1..gamma_6, ext gamma_7/gamma_8,
# and the gamma_5 EXT layer control
SLOTS = ([("committed", g) for g in r80.GAMMAS]
         + [("ext", r94.G7), ("ext", r94.G8), ("ext", r94.G5)])
# the six record-2024 P1 slots (the ones whose delta 0.10 string is not in the
# record-2021 C1 artifact)
P1_SLOTS = [("committed", r80.GAMMAS[1]), ("committed", r80.GAMMAS[2]),
            ("committed", r80.GAMMAS[4]), ("committed", r80.GAMMAS[5]),
            ("ext", r94.G7), ("ext", r94.G8)]
# the three EXT slots the 0.001 refinement targets
U_SLOTS = [("ext", r94.G7), ("ext", r94.G8), ("ext", r94.G5)]


def grid(step):
    lo, hi = RANGE
    count = int(round((hi - lo) / step)) + 1
    return [round(lo + step * i, 6) for i in range(count)]


def key(layer, gk, delta, scale, dxi):
    return (layer, round(gk, 6), round(delta, 6), round(scale, 6),
            round(dxi, 6))


def load(name):
    with open(os.path.join(REPO, "results", name), encoding="utf-8") as stream:
        blob = json.load(stream)
    top_dxi = blob.get("dxi", DXI)
    out = {}
    for row in blob["rows"]:
        dxi = row.get("dxi", top_dxi)
        out[key(row["layer"], row["gamma"], row["delta"], row["scale"],
                 dxi)] = row
    return out


def present(rows, layer, gk, delta, scales):
    out = []
    for sc in scales:
        if key(layer, gk, delta, sc, DXI) in rows:
            out.append(sc)
    return out


def main():
    floor = load("2012_cover_scan_rows_floor.json")
    p1 = load("2024_ladder9_rows.json")
    c1 = load("2021_scale_ladder_rows.json")
    union002005 = sorted(set(grid(0.005)) | set(grid(0.002)))
    census = {
        "record": 2026,
        "generated_from": [
            "results/2012_cover_scan_rows_floor.json",
            "results/2024_ladder9_rows.json",
            "results/2021_scale_ladder_rows.json"],
        "rule": ("docs/proofs/2026_ladder_refinement_preregistration.md "
                 "section 2"),
        "range": list(RANGE),
        "dxi": DXI,
    }

    # ---- U: the 0.001 grid at delta 0.10 on the three EXT slots
    u = {"delta": 0.10, "step": 0.001, "slots": {}, "missing_preload": []}
    u_total = 0
    for layer, gk in U_SLOTS:
        pre = present(floor, layer, gk, 0.10, union002005)
        pre += [sc for sc in present(p1, layer, gk, 0.10, union002005)
                if sc not in pre]
        pre += [sc for sc in present(c1, layer, gk, 0.10, union002005)
                if sc not in pre]
        pre = sorted(set(pre))
        new = [sc for sc in grid(0.001)
               if not any(abs(sc - p) < 1e-9 for p in pre)]
        if not pre:
            u["missing_preload"].append("%s:%.6f" % (layer, gk))
        u["slots"]["%s:%.6f" % (layer, gk)] = {
            "layer": layer, "gamma": gk, "preloaded": pre,
            "new_scales": new, "new_cells": len(new)}
        u_total += len(new)
    u["new_cells"] = u_total
    census["u"] = u

    # ---- D: the 0.002 grid at delta 0.02 / 0.05 on the six P1 slots
    d = {"step": 0.002, "deltas": [0.02, 0.05], "slots": {},
         "missing_preload": []}
    d_total = 0
    for layer, gk in P1_SLOTS:
        entry = {"layer": layer, "gamma": gk, "reference_delta": 0.10,
                 "reference_present": len(present(
                     p1, layer, gk, 0.10, grid(0.002))) == len(grid(0.002)),
                 "deltas": {}}
        for delta in (0.02, 0.05):
            pre = present(floor, layer, gk, delta, FIVE_POINT)
            new = [sc for sc in grid(0.002)
                   if not any(abs(sc - p) < 1e-9 for p in pre)]
            if len(pre) != len(FIVE_POINT):
                d["missing_preload"].append(
                    "%s:%.6f d=%.2f" % (layer, gk, delta))
            entry["deltas"]["%.3f" % delta] = {
                "preloaded": pre, "new_scales": new, "new_cells": len(new)}
            d_total += len(new)
        d["slots"]["%s:%.6f" % (layer, gk)] = entry
    d["new_cells"] = d_total
    census["d"] = d

    # ---- S: the zero-measurement five-point string census
    s = {"deltas": list(DELTAS), "scales": list(FIVE_POINT), "slots": {},
         "missing": []}
    for layer, gk in SLOTS:
        entry = {"layer": layer, "gamma": gk, "deltas": {}}
        for delta in DELTAS:
            pre = present(floor, layer, gk, delta, FIVE_POINT)
            entry["deltas"]["%.2f" % delta] = pre
            if len(pre) != len(FIVE_POINT):
                s["missing"].append("%s:%.6f d=%.2f" % (layer, gk, delta))
        s["slots"]["%s:%.6f" % (layer, gk)] = entry
    census["s"] = s

    out = os.path.join(REPO, "results", "2026_registered_cells.json")
    with open(out, "w", encoding="utf-8") as stream:
        json.dump(census, stream, indent=1)
        stream.write("\n")
    print("wrote", out)
    print("U new cells", u["new_cells"], "missing preload", u["missing_preload"])
    print("D new cells", d["new_cells"], "missing preload", d["missing_preload"])
    print("S missing cells", s["missing"])
    print("D reference complete",
          all(v["reference_present"] for v in d["slots"].values()))


if __name__ == "__main__":
    main()
