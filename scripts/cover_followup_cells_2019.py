#!/usr/bin/env python3
"""Record 2019: cell lists for the COVER follow-ups (M1 edge re-read, M2 floor
refinement), GENERATED from the committed record-2012 artifacts.

Both lists are mechanical applications of the rules fixed in
docs/proofs/2019_cover_resolution_refinement_preregistration.md section 2 and
are never typed by hand (the project's anchor-table rule, third recurrence
caught in record 2018 section 4):

  M1  band-edge cells of the delta = 0.10 comb.  Per (layer, height) the
      certified C-sign is read along the 21-point scale grid; every cell lying
      between two consecutive certified cells of opposite sign is an edge cell,
      and a certified C > 0 run that touches a window edge (scale 0.80 or
      1.00) has its window-side cells included too.

  M2  the registered slots (the eight registered heights plus the gamma_5 EXT
      layer control) and, per slot, the certified host scales at delta = 0.02
      that lie inside the five-point grid {0.86, ..., 0.94} - the record-2017
      section 5 "hosts sit inside the five-point grid" list.

Read-only: no measurement, no import of the rig.  Writes
results/2019_registered_cells.json.
"""

import json
import os

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
WIDTH_ROWS = os.path.join(REPO, "results", "2012_cover_scan_rows_width.json")
FLOOR_ROWS = os.path.join(REPO, "results", "2012_cover_scan_rows_floor.json")
FLOOR_VERDICT = os.path.join(REPO, "results", "2012_cover_delta_floor.json")
OUT = os.path.join(REPO, "results", "2019_registered_cells.json")

SCALES = [round(0.80 + 0.01 * i, 2) for i in range(21)]
FIVE_POINT = (0.86, 0.88, 0.90, 0.92, 0.94)
WIDTH_DELTA = 0.10
FLOOR_DELTA = 0.02
EPS = 1e-9


def load(path):
    with open(path, encoding="utf-8") as stream:
        return json.load(stream)


def sign_of(row):
    if not row["certified"]:
        return "u"
    return "+" if row["C"] > 0.0 else "-"


def edge_indices(signs):
    """Cells between consecutive certified cells of opposite sign, plus the
    certified '+' window-edge runs."""
    idx = [i for i, s in enumerate(signs) if s != "u"]
    edges = set()
    for a, b in zip(idx, idx[1:]):
        if signs[a] != signs[b]:
            edges.update(range(a, b + 1))
    if idx and signs[idx[0]] == "+":
        edges.update(range(0, idx[0] + 1))
    if idx and signs[idx[-1]] == "+":
        edges.update(range(idx[-1], len(signs)))
    return sorted(edges)


def key_of(layer, gk):
    return "%s:%.6f" % (layer, gk)


def main():
    width = load(WIDTH_ROWS)
    floor = load(FLOOR_ROWS)
    floor_verdict = load(FLOOR_VERDICT)
    wrows, frows = width["rows"], floor["rows"]
    print("width rows %d (dxi %s), floor rows %d (dxi %s)"
          % (len(wrows), width.get("dxi"), len(frows), floor.get("dxi")))

    # ---------------------------------------------------------------- M1
    m1_heights = sorted(set((r["layer"], r["gamma"]) for r in wrows))
    m1 = {}
    edge_cells = {}
    full_cells = {}
    for layer, gk in m1_heights:
        cells = [r for r in wrows
                 if r["layer"] == layer and abs(r["gamma"] - gk) < EPS
                 and abs(r["delta"] - WIDTH_DELTA) < EPS]
        cells.sort(key=lambda r: r["scale"])
        scales = [r["scale"] for r in cells]
        if scales != SCALES:
            raise SystemExit("%s: width slice is not the 21-point grid: %s"
                             % (key_of(layer, gk), scales))
        signs = "".join(sign_of(r) for r in cells)
        bands = []
        cur = 0
        for s in signs:
            if s == "+":
                cur += 1
            elif cur:
                bands.append(cur)
                cur = 0
        if cur:
            bands.append(cur)
        edges = edge_indices(signs)
        m1[key_of(layer, gk)] = {
            "layer": layer, "gamma": gk, "signs": signs,
            "n_c_positive": sum(1 for s in signs if s == "+"),
            "n_bands": len(bands), "band_widths": bands,
            "edge_scales": [scales[i] for i in edges],
            "n_edge": len(edges),
        }
        for i in edges:
            edge_cells[(layer, gk, scales[i])] = True
        for sc in SCALES:
            full_cells[(layer, gk, sc)] = True

    r_keys = [key_of(layer, gk) for layer, gk in m1_heights
              if layer == "committed"][:2]
    m1_cells = [{"layer": layer, "gamma": gk, "delta": WIDTH_DELTA,
                 "scale": sc} for (layer, gk, sc) in sorted(full_cells)]
    m1_edge_cells = [{"layer": layer, "gamma": gk, "delta": WIDTH_DELTA,
                      "scale": sc} for (layer, gk, sc) in sorted(edge_cells)]
    print("\nM1 delta 0.10 slices (committed 0.004 reading), per slot:")
    for key in sorted(m1):
        entry = m1[key]
        print("  %-24s signs %s  bands %d %s  edges %d"
              % (key, entry["signs"], entry["n_bands"], entry["band_widths"],
                 entry["n_edge"]))
    print("M1 full-slice re-read cells: %d (nine slots x 21 scales)"
          % len(m1_cells))
    print("M1 registered edge subset: %d cells" % len(m1_edge_cells))
    print("M1 eps/r table heights (committed layer, first two): %s"
          % ", ".join(r_keys))

    # ---------------------------------------------------------------- M2
    fkeys = sorted(set((r["layer"], r["gamma"]) for r in frows))
    m2_slots = {}
    for layer, gk in fkeys:
        hosts = sorted(r["scale"] for r in frows
                       if r["layer"] == layer and abs(r["gamma"] - gk) < EPS
                       and abs(r["delta"] - FLOOR_DELTA) < EPS
                       and any(abs(r["scale"] - p) < EPS for p in FIVE_POINT)
                       and r["host"])
        committed_floor = floor_verdict["floors"].get(key_of(layer, gk), {})
        m2_slots[key_of(layer, gk)] = {
            "layer": layer, "gamma": gk,
            "five_point_hosts_at_0.02": hosts,
            "inside": bool(hosts),
            "committed_floor": committed_floor.get("floor"),
        }
    inside = [k for k, v in sorted(m2_slots.items()) if v["inside"]]
    outside = [k for k, v in sorted(m2_slots.items()) if not v["inside"]]
    print("\nM2 slots with five-point hosts at delta 0.02: %s" % ", ".join(inside))
    print("M2 slots without (committed stage-B sweep territory): %s"
          % (", ".join(outside) or "(none)"))

    out = {
        "record": "2019",
        "generated_from": [
            "results/2012_cover_scan_rows_width.json",
            "results/2012_cover_scan_rows_floor.json",
            "results/2012_cover_delta_floor.json",
        ],
        "rule": "docs/proofs/2019_cover_resolution_refinement_preregistration.md"
                " section 2",
        "m1": {"delta": WIDTH_DELTA, "scales": SCALES, "heights": m1,
               "r_table_keys": r_keys, "cells": m1_cells,
               "edge_cells": m1_edge_cells,
               "n_cells": len(m1_cells), "n_edge_cells": len(m1_edge_cells)},
        "m2": {"delta_host_reading": FLOOR_DELTA, "five_point": list(FIVE_POINT),
               "slots": m2_slots, "inside": inside, "outside": outside},
    }
    with open(OUT, "w", encoding="utf-8") as stream:
        json.dump(out, stream, indent=2)
        stream.write("\n")
    print("\nresults -> %s" % OUT)


if __name__ == "__main__":
    main()