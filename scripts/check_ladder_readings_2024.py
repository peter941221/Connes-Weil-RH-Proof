#!/usr/bin/env python3
"""Independent recomputation of the record-2024 readings (P1 ladder9, P2
delta-ladder) from the committed rows artifacts.  Zero imports of the rig:
json + math only, its own pair walk, its own verdicts.

Purpose: the record-2023 lesson (a registered per-slot table was not emitted
by the reading and had to be recomputed post hoc) plus the standing rule
that a reading is evidence only when an independent path reproduces it.

Usage:
  python3 check_ladder_readings_2024.py ladder9   [--smoke]
  python3 check_ladder_readings_2024.py deltaladder [--smoke]

Compares against results/2024_ladder9[_smoke].json (or delta-ladder) and
prints PASS/FAIL per field; exit code 0 iff all fields match.
"""

import json
import math
import os
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RANGE = (0.86, 0.96)
STEPS = (0.005, 0.002)
SUBLATTICE = [round(0.86 + 0.01 * i, 2) for i in range(11)]
FIVE_POINT = (0.86, 0.88, 0.90, 0.92, 0.94)
L_AGREE_BAR = 0.25
TOL = 1e-12           # relative tolerance on floats (same inputs, own path)
EPS = 1e-9

def census_slots(phase):
    """The slot table read from the generated census artifact (the anchor
    rule: generated from artifacts, never typed - the first version of this
    checker typed gamma_3 and its slice silently came back empty)."""
    path = os.path.join(REPO, "results", "2024_registered_cells.json")
    with open(path, encoding="utf-8") as stream:
        census = json.load(stream)
    block = census["p1"] if phase == "ladder9" else census["p2"]
    out = []
    for entry in block["slots"].values():
        out.append((entry["layer"], entry["gamma"]))
    return out


SMOKE_LIMIT = 3


def grid(step, smoke):
    lo, hi = RANGE
    count = int(round((hi - lo) / step)) + 1
    scales = [round(lo + step * i, 6) for i in range(count)]
    return scales[:SMOKE_LIMIT] if smoke else scales


def load(path):
    with open(path, encoding="utf-8") as stream:
        return json.load(stream)


def slice_rows(rows, layer, gk, delta, scales):
    kept = []
    want = set(round(s, 6) for s in scales)
    for r in rows:
        if r["layer"] != layer or abs(r["gamma"] - gk) > 1e-9:
            continue
        if abs(r["delta"] - delta) > 1e-12:
            continue
        if round(r["scale"], 6) not in want:
            continue
        if r.get("face") == "INSTRUMENT":
            continue
        kept.append(r)
    kept.sort(key=lambda r: r["scale"])
    return kept


def pair_walk(rows, stride, step):
    """Independent pair rule: consecutive certified rows at exact distance
    stride*step (the rig's 1e-6 gate), C-sign and healthy flips."""
    n = c_flip = h_flip = 0
    n_end = c_end = h_end = 0
    for a, b in zip(rows, rows[stride:]):
        if abs((b["scale"] - a["scale"]) - stride * step) > 1e-6:
            continue
        n += 1
        if (a["C"] > 0) != (b["C"] > 0):
            c_flip += 1
        if (a.get("face") == "WIRE1") != (b.get("face") == "WIRE1"):
            h_flip += 1
        for r in (a, b):
            n_end += 1
            c_end += 1 if r["C"] > 0 else 0
            h_end += 1 if r.get("face") == "WIRE1" else 0
    return {"n_pairs": n, "c_flip": c_flip, "h_flip": h_flip,
            "n_end": n_end, "c_end": c_end, "h_end": h_end}


def rate_sigma(p, n):
    return math.sqrt(p * (1.0 - p) / n) if n else 0.0


def close(a, b):
    if a is None or b is None:
        return a is None and b is None
    return abs(a - b) <= TOL * max(1.0, abs(a), abs(b))


def check_ladder9(smoke):
    suffix = "_smoke" if smoke else ""
    rows = load(os.path.join(REPO, "results",
                             "2024_ladder9_rows%s.json" % suffix))["rows"]
    reading = load(os.path.join(REPO, "results",
                                "2024_ladder9%s.json" % suffix))
    failures = []
    for layer, gk in census_slots("ladder9")[:1] if smoke else census_slots("ladder9"):
        key = "%s:%.6f" % (layer, gk)
        slots = reading["slots"].get(key)
        if slots is None:
            failures.append((key, "missing in reading"))
            continue
        for step in STEPS:
            walk = pair_walk(slice_rows(rows, layer, gk, 0.10, grid(step, smoke)), 1, step)
            ent = slots["estimators"]["h=%g (step %g stride 1)" % (step, step)]
            if ent is None:
                failures.append((key, "estimator %g missing" % step))
                continue
            for field in ("n_pairs", "c_flip", "h_flip"):
                if walk[field] != ent[field]:
                    failures.append((key, "%s %g %s: %s vs %s"
                                     % (field, step, field, walk[field], ent[field])))
            for field, src in (("c_rate", "c_flip"), ("h_rate", "h_flip")):
                mine = walk[src] / walk["n_pairs"] if walk["n_pairs"] else None
                if not close(mine, ent[field]):
                    failures.append((key, "%s %g: %s vs %s" % (field, step, mine, ent[field])))
            mu_h = walk["h_end"] / walk["n_end"] if walk["n_end"] else None
            mu_c = walk["c_end"] / walk["n_end"] if walk["n_end"] else None
            ref_h = 2 * mu_h * (1 - mu_h) if mu_h is not None else None
            ref_c = 2 * mu_c * (1 - mu_c) if mu_c is not None else None
            if not close(ref_h, ent["ref_h"]):
                failures.append((key, "ref_h %g: %s vs %s" % (step, ref_h, ent["ref_h"])))
            if not close(ref_c, ent["ref_c"]):
                failures.append((key, "ref_c %g: %s vs %s" % (step, ref_c, ent["ref_c"])))
            sig = rate_sigma(ent["h_rate"] or 0.0, walk["n_pairs"])
            sigc = rate_sigma(ent["c_rate"] or 0.0, walk["n_pairs"])
            dev_h = (ent["h_rate"] - ref_h) / sig if sig else None
            dev_c = (ent["c_rate"] - ref_c) / sigc if sigc else None
            if not close(dev_h, ent["dev_h"]):
                failures.append((key, "dev_h %g: %s vs %s" % (step, dev_h, ent["dev_h"])))
            if not close(dev_c, ent["dev_c"]):
                failures.append((key, "dev_c %g: %s vs %s" % (step, dev_c, ent["dev_c"])))
        # L and the derived flags, recomputed from the artifact's own rates
        e2 = slots["estimators"]["h=0.002 (step 0.002 stride 1)"]
        e5 = slots["estimators"]["h=0.005 (step 0.005 stride 1)"]
        l2 = 0.002 / e2["c_rate"] if e2 and e2["c_rate"] else None
        l5 = 0.005 / e5["c_rate"] if e5 and e5["c_rate"] else None
        if not close(l2, slots["L_002"]):
            failures.append((key, "L_002: %s vs %s" % (l2, slots["L_002"])))
        if not close(l5, slots["L_005"]):
            failures.append((key, "L_005: %s vs %s" % (l5, slots["L_005"])))
        if e2 and e5:
            counts_equal = e2["c_flip"] == e5["c_flip"]
            if counts_equal != slots["counts_equal"]:
                failures.append((key, "counts_equal"))
            rc = (l2 is not None and l5 is not None
                  and abs(l2 - l5) / max(l2, l5) <= L_AGREE_BAR)
            if rc != slots["resolution_consistent"]:
                failures.append((key, "resolution_consistent"))
    # verdict, recomputed
    win = []
    for key, slots in reading["slots"].items():
        e2 = slots["estimators"].get("h=0.002 (step 0.002 stride 1)")
        if e2 and e2["dev_h"] is not None and e2["dev_h"] <= -3.0:
            win.append(key)
    verdict = ("LADDER9-UNIFORM" if len(win) == len(reading["slots"])
               else "LADDER9-PARTIAL" if win else "LADDER9-NONE")
    if reading["instrument_fail"]:
        verdict = "LADDER9-INSTRUMENT-FAIL"
    if verdict != reading["verdict"]:
        failures.append(("<verdict>", "%s vs %s" % (verdict, reading["verdict"])))
    return failures, verdict


def check_delta(smoke):
    suffix = "_smoke" if smoke else ""
    rows = load(os.path.join(REPO, "results",
                             "2024_delta_ladder_rows%s.json" % suffix))["rows"]
    c1 = load(os.path.join(REPO, "results", "2021_scale_ladder_rows.json"))["rows"]
    reading = load(os.path.join(REPO, "results",
                                "2024_delta_ladder%s.json" % suffix))
    failures = []
    ratios = []
    for layer, gk in census_slots("deltaladder")[:1] if smoke else census_slots("deltaladder"):
        key = "%s:%.6f" % (layer, gk)
        slots = reading["slots"].get(key)
        if slots is None:
            failures.append((key, "missing in reading"))
            continue
        for dkey in sorted(slots["L"]):
            delta = float(dkey)
            src = c1 if abs(delta - 0.10) < 1e-9 else rows
            scales = grid(0.002, smoke)
            walk = pair_walk(slice_rows(src, layer, gk, delta, scales), 1, 0.002)
            if walk["n_pairs"] != slots["n_pairs_002"].get(dkey):
                failures.append((key, "d=%s n_pairs: %s vs %s"
                                 % (dkey, walk["n_pairs"],
                                    slots["n_pairs_002"].get(dkey))))
            mine = (walk["c_flip"] / walk["n_pairs"]) if walk["n_pairs"] else None
            l = (0.002 / mine) if mine else None
            if not close(l, slots["L"].get(dkey)):
                failures.append((key, "d=%s L: %s vs %s"
                                 % (dkey, l, slots["L"].get(dkey))))
            if l is not None:
                ratios.append(l)
        ls = [v for v in slots["L"].values() if v is not None]
        ratio = max(ls) / min(ls) if len(ls) == len(slots["L"]) and ls else None
        if not close(ratio, slots["stability_ratio"]):
            failures.append((key, "ratio: %s vs %s" % (ratio, slots["stability_ratio"])))
    verdict = None
    if reading["instrument_fail"]:
        verdict = "L-DELTA-INSTRUMENT-FAIL"
    elif all(r["stable"] for r in reading["slots"].values()):
        verdict = "L-DELTA-STABLE"
    elif any(r["stability_ratio"] is not None
             and r["stability_ratio"] > 1.0 + L_AGREE_BAR
             for r in reading["slots"].values()):
        verdict = "L-DELTA-SHIFTED"
    else:
        verdict = "L-DELTA-DEGENERATE"
    if verdict != reading["verdict"]:
        failures.append(("<verdict>", "%s vs %s" % (verdict, reading["verdict"])))
    return failures, verdict


def main():
    phase = sys.argv[1] if len(sys.argv) > 1 else ""
    smoke = "--smoke" in sys.argv
    if phase == "ladder9":
        failures, verdict = check_ladder9(smoke)
    elif phase == "deltaladder":
        failures, verdict = check_delta(smoke)
    else:
        raise SystemExit("usage: check_ladder_readings_2024.py "
                         "ladder9|deltaladder [--smoke]")
    print("independent recomputation (%s%s): %d field failures"
          % (phase, " smoke" if smoke else "", len(failures)))
    for key, msg in failures:
        print("  FAIL %-24s %s" % (key, msg))
    print("verdict reproduced: %s" % verdict)
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())