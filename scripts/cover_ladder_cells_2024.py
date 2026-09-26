#!/usr/bin/env python3
"""Record 2024: cell census for the L-ladder wave (P1 nine-slot ladder, P2
delta probe), GENERATED from the committed artifacts.

The two phases are fixed in docs/proofs/2024_l_ladder_preregistration.md
section 2 and every cell list here is a mechanical application of those rules,
never typed by hand (the project's anchor-table rule, fourth recurrence):

  P1  the record-2021 C1 ladder (grids 0.005 and 0.002 over scale in
      [0.86, 0.96] at delta = 0.10) on the six slots C1 did not measure:
      committed gamma_2 .. gamma_5 (indices 1, 2, 4, 5) and the two EXT
      heights gamma_7, gamma_8.  The 0.01-spaced sublattice (11 points) is
      preloaded from the committed width rows; 50 new cells per slot.

  P2  the same two grids on the three C1 slots at delta = 0.02 and 0.05.
      The five-point cells {0.86, .., 0.94} at these deltas are preloaded
      from the committed floor rows; 56 new cells per (slot, delta).  The
      delta = 0.10 reference row for the delta table is the committed C1
      rows artifact, never re-measured.

Read-only: no measurement, no import of the rig.  Writes
results/2024_registered_cells.json.
"""

import json
import os

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
WIDTH_ROWS = os.path.join(REPO, "results", "2012_cover_scan_rows_width.json")
FLOOR_ROWS = os.path.join(REPO, "results", "2012_cover_scan_rows_floor.json")
C1_ROWS = os.path.join(REPO, "results", "2021_scale_ladder_rows.json")
OUT = os.path.join(REPO, "results", "2024_registered_cells.json")

RANGE = (0.86, 0.96)
STEPS = (0.005, 0.002)
SUBLATTICE = [round(0.86 + 0.01 * i, 2) for i in range(11)]
FIVE_POINT = (0.86, 0.88, 0.90, 0.92, 0.94)
WIDTH_DELTA = 0.10
NEW_DELTAS = (0.02, 0.05)
REFERENCE_DELTA = 0.10
DETERMINISM_SCALES = (0.88, 0.90, 0.92)
EPS = 1e-9

# the six slots P1 adds (the record-2021 C1 slots are gamma_1, gamma_4,
# committed gamma_5-through-EXT-control; P1 completes the registered nine)
P1_SLOTS = [("committed", "gamma_2"), ("committed", "gamma_3"),
            ("committed", "gamma_5"), ("committed", "gamma_6"),
            ("ext", "gamma_7"), ("ext", "gamma_8")]
# the three C1 slots (by their record-2021 names, resolved below from the
# committed artifacts, never hard-coded here)
P2_SLOT_KEYS = ["committed:%.6f" % 14.134725141734695,
                "committed:%.6f" % 27.67032193035704,
                "ext:%.6f" % 30.424876125859512]


def load(path):
    with open(path, encoding="utf-8") as stream:
        return json.load(stream)


def grid(step):
    lo, hi = RANGE
    count = int(round((hi - lo) / step)) + 1
    return [round(lo + step * i, 6) for i in range(count)]


def main():
    width = load(WIDTH_ROWS)
    floor = load(FLOOR_ROWS)
    c1 = load(C1_ROWS)
    wrows, frows, crows = width["rows"], floor["rows"], c1["rows"]
    print("width rows %d (dxi %s); floor rows %d (dxi %s); C1 rows %d "
          "(dxi %s)" % (len(wrows), width.get("dxi"), len(frows),
                        floor.get("dxi"), len(crows), c1.get("dxi")))
    grids = {step: grid(step) for step in STEPS}

    # resolve every slot from the committed artifacts by its own key
    wkeys = {}
    for r in wrows:
        wkeys.setdefault("%s:%.6f" % (r["layer"], round(r["gamma"], 6)),
                         (r["layer"], r["gamma"]))
    ckeys = {}
    for r in crows:
        ckeys.setdefault("%s:%.6f" % (r["layer"], round(r["gamma"], 6)),
                         (r["layer"], r["gamma"]))

    def resolve(name):
        for table in (wkeys, ckeys):
            if name in table:
                return table[name]
        raise SystemExit("slot %s not found in the committed artifacts" % name)

    union = sorted(set(grids[0.005]) | set(grids[0.002]))

    def new_positions(preload):
        return len([sc for sc in union
                    if not any(abs(sc - p) < EPS for p in preload)])

    # ---------------------------------------------------------------- P1
    p1_slots, p1_missing, p1_new = {}, [], 0
    committed_by_key = {}
    for r in wrows:
        if abs(r["delta"] - WIDTH_DELTA) < EPS:
            committed_by_key.setdefault(
                (r["layer"], round(r["gamma"], 6)), {})[round(r["scale"], 6)] = r
    # the registered order (gamma_1 .. gamma_6 committed, gamma_7/gamma_8 EXT)
    # is read off the artifacts themselves, never typed
    comm = sorted(set((r["layer"], round(r["gamma"], 6)) for r in wrows
                      if r["layer"] == "committed"))
    ext_all = sorted(set(round(r["gamma"], 6) for r in wrows
                         if r["layer"] == "ext"))
    # the EXT layer carries three slots: the gamma_5 layer control (whose
    # height also appears among the committed heights) and gamma_7, gamma_8
    comm_gammas = set(gk for _layer, gk in comm)
    ext_control = [gk for gk in ext_all if gk in comm_gammas]
    ext_heights = [gk for gk in ext_all if gk not in comm_gammas]
    if len(ext_control) != 1 or len(ext_heights) != 2:
        raise SystemExit("EXT layer is not control + gamma_7/gamma_8: %s"
                         % ext_all)
    by_tag = {}
    for i, (layer, gk) in enumerate(comm, start=1):
        by_tag["committed:gamma_%d" % i] = (layer, gk)
    by_tag["ext:gamma_7"] = ("ext", ext_heights[0])
    by_tag["ext:gamma_8"] = ("ext", ext_heights[1])
    by_tag["ext:gamma_5_control"] = ("ext", ext_control[0])
    for layer, tag in P1_SLOTS:
        key = "%s:%s" % (layer, tag)
        if key not in by_tag:
            raise SystemExit("P1 slot %s did not resolve" % key)
        slot = by_tag[key]
        scales_present = committed_by_key.get(slot, {})
        sub_ok = all(any(abs(s - p) < EPS for s in scales_present)
                     for p in SUBLATTICE)
        if not sub_ok:
            p1_missing.append([slot[0], slot[1]])
        new = new_positions(SUBLATTICE)
        p1_new += new
        p1_slots["%s:%.6f" % slot] = {
            "layer": slot[0], "gamma": slot[1],
            "preloaded_sublattice": list(SUBLATTICE),
            "preloaded_present": sub_ok, "new_cells": new,
            "det_scales": list(DETERMINISM_SCALES)}
    print("\nP1 new cells: %d (six slots x %d)" % (p1_new, p1_new // 6))

    # ---------------------------------------------------------------- P2
    floor_by = {}
    for r in frows:
        floor_by.setdefault((r["layer"], round(r["gamma"], 6),
                             round(r["delta"], 3)), {})[round(r["scale"], 6)] = r
    p2_slots, p2_missing, p2_new = {}, [], 0
    for name in P2_SLOT_KEYS:
        layer, gk = resolve(name)
        entry = {"layer": layer, "gamma": gk, "deltas": {}}
        for delta in NEW_DELTAS:
            have = floor_by.get((layer, round(gk, 6), round(delta, 3)), {})
            sub_ok = all(any(abs(s - p) < EPS for s in have)
                         for p in FIVE_POINT)
            if not sub_ok:
                p2_missing.append([layer, gk, delta])
            new = new_positions(FIVE_POINT)
            p2_new += new
            entry["deltas"]["%.3f" % delta] = {
                "preloaded_five_point": list(FIVE_POINT),
                "preloaded_present": sub_ok, "new_cells": new,
                "det_scales": list(DETERMINISM_SCALES)}
        p2_slots[name] = entry
    # the delta = 0.10 reference must be complete in the committed C1 rows
    ref_check = {}
    for name in P2_SLOT_KEYS:
        layer, gk = resolve(name)
        have = set(round(r["scale"], 6) for r in crows
                   if r["layer"] == layer and abs(r["gamma"] - gk) < EPS
                   and abs(r["delta"] - REFERENCE_DELTA) < EPS
                   and abs(r.get("dxi", 0.004) - 0.004) < EPS)
        ref_check[name] = {
            "cells": len(have),
            "complete": all(any(abs(s - p) < EPS for s in have)
                            for step in STEPS for p in grids[step])}
    print("P2 new cells: %d (three slots x 2 deltas x %d)"
          % (p2_new, p2_new // 6))
    print("P2 delta 0.10 reference complete: %s"
          % all(v["complete"] for v in ref_check.values()))

    out = {
        "record": "2024",
        "generated_from": [
            "results/2012_cover_scan_rows_width.json",
            "results/2012_cover_scan_rows_floor.json",
            "results/2021_scale_ladder_rows.json",
        ],
        "rule": "docs/proofs/2024_l_ladder_preregistration.md section 2",
        "range": list(RANGE), "steps": list(STEPS),
        "grids": {("%g" % step): grids[step] for step in STEPS},
        "p1": {"slots": p1_slots, "missing_preload": p1_missing,
               "new_cells": p1_new, "delta": WIDTH_DELTA,
               "preload_source": "results/2012_cover_scan_rows_width.json"},
        "p2": {"slots": p2_slots, "missing_preload": p2_missing,
               "new_cells": p2_new, "new_deltas": list(NEW_DELTAS),
               "reference_delta": REFERENCE_DELTA,
               "reference_source": "results/2021_scale_ladder_rows.json",
               "reference_check": ref_check,
               "preload_source": "results/2012_cover_scan_rows_floor.json"},
    }
    with open(OUT, "w", encoding="utf-8") as stream:
        json.dump(out, stream, indent=2)
        stream.write("\n")
    print("\nresults -> %s" % OUT)


if __name__ == "__main__":
    main()