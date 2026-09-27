#!/usr/bin/env python3
"""Independent recomputation of the record-2026 readings (U ultrafine, D
string-delta, S string-census) from the committed rows artifacts.  Zero
imports of the rig: json + math only, its own pair walk, its own string
walk, its own verdicts.

Purpose: the standing rule that a reading is evidence only when a second,
independent path reproduces it.  The record-2024 wave's checker caught a
unit-scale defect (L_005 computed with the 0.002 step) within minutes of its
first run; this is the same instrument for the 2026 readings.

Usage:
  python3 check_ladder_readings_2026.py ultrafine    [--smoke]
  python3 check_ladder_readings_2026.py stringdelta  [--smoke]
  python3 check_ladder_readings_2026.py stringcensus [--smoke]

Compares against results/2026_<name>[_smoke].json and prints PASS/FAIL per
field; exit code 0 iff all fields match.
"""

import json
import math
import os
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RANGE = (0.86, 0.96)
U_STEPS = (0.005, 0.002, 0.001)
D_STEP = 0.002
D_DELTAS = (0.02, 0.05)
D_REFERENCE = 0.10
S_DELTAS = (0.02, 0.05, 0.10, 0.15, 0.20, 0.30)
S_SCALES = (0.86, 0.88, 0.90, 0.92, 0.94)
L_AGREE_BAR = 0.25
SMOKE_LIMIT = 3
TOL = 1e-12
EPS = 1e-9

CENSUS = "2026_registered_cells.json"
ROWS = {
    "ultrafine": "2026_ultrafine_rows",
    "stringdelta": "2026_string_delta_rows",
    "stringcensus": "2026_string_census_rows",
}
READING = {
    "ultrafine": "2026_ultrafine",
    "stringdelta": "2026_string_delta",
    "stringcensus": "2026_string_census",
}
BLOCK = {"ultrafine": "u", "stringdelta": "d", "stringcensus": "s"}


def load(name):
    with open(os.path.join(REPO, "results", name), encoding="utf-8") as fh:
        return json.load(fh)


def census_slots(phase):
    """The registered slot table, read from the GENERATED census artifact
    (the anchor rule: generated from artifacts, never typed)."""
    block = load(CENSUS)[BLOCK[phase]]
    out = []
    for entry in block["slots"].values():
        out.append((entry["layer"], entry["gamma"]))
    return out


def grid(step, smoke):
    lo, hi = RANGE
    count = int(round((hi - lo) / step)) + 1
    scales = [round(lo + step * i, 6) for i in range(count)]
    return scales[:SMOKE_LIMIT] if smoke else scales


def slice_rows(rows, layer, gk, delta, scales):
    """Certified rows of one cell set, on the rig's own filter (INSTRUMENT
    rows dropped), sorted by scale."""
    want = set(round(s, 6) for s in scales)
    kept = []
    for row in rows:
        if row["layer"] != layer or abs(row["gamma"] - gk) > EPS:
            continue
        if abs(row["delta"] - delta) > 1e-12:
            continue
        if round(row["scale"], 6) not in want:
            continue
        if row.get("face") == "INSTRUMENT":
            continue
        kept.append(row)
    kept.sort(key=lambda row: row["scale"])
    return kept


def pair_walk(rows, stride, step):
    """Independent pair rule: rows at exact scale distance stride*step, the
    rig's 1e-6 adjacency gate."""
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
        for row in (a, b):
            n_end += 1
            c_end += 1 if row["C"] > 0 else 0
            h_end += 1 if row.get("face") == "WIRE1" else 0
    return {"n_pairs": n, "c_flip": c_flip, "h_flip": h_flip,
            "n_end": n_end, "c_end": c_end, "h_end": h_end}


def sign_string(rows):
    """The C sign string: scale -> '+'/'-' over rows with a readable C (an
    INSTRUMENT or non-finite row is a gap, never guessed)."""
    out = {}
    for row in rows:
        if row.get("face") == "INSTRUMENT":
            continue
        c = row.get("C")
        if c is None or not math.isfinite(c):
            continue
        out[round(row["scale"], 6)] = "+" if c > 0.0 else "-"
    return out


def key_str(x):
    """Canonical scale key.  The rig keys its strings by the rounded float,
    which json writes as e.g. '0.86'; this side normalizes both directions so
    a key-format difference can never read as a sign difference."""
    return "%.6f" % round(float(x), 6)


def norm_str(seq):
    return {key_str(k): v for k, v in seq.items()}


def norm_nested(blob):
    return {k: norm_str(v) for k, v in blob.items()}


def norm_list(items):
    return sorted(key_str(x) for x in items)


def compare(ref, other):
    """(disagreements, n_common, only_reference, only_other) over the common
    scales of two strings keyed '%.6f'."""
    common = sorted(set(ref) & set(other))
    k = sum(1 for sc in common if ref[sc] != other[sc])
    return (k, len(common), sorted(set(ref) - set(other)),
            sorted(set(other) - set(ref)))


def flips_of(seq, scales):
    k = n = 0
    prev = None
    for sc in sorted(scales):
        sign = seq.get(round(sc, 6))
        if sign is None:
            prev = None
            continue
        if prev is not None:
            n += 1
            if sign != prev:
                k += 1
        prev = sign
    return k, n


def flip_lefts(rows, stride, step):
    out = []
    for a, b in zip(rows, rows[stride:]):
        if abs((b["scale"] - a["scale"]) - stride * step) > 1e-6:
            continue
        if (a["C"] > 0) != (b["C"] > 0):
            out.append(a["scale"])
    return out


def min_gap(lefts):
    if len(lefts) < 2:
        return None
    return min(b - a for a, b in zip(lefts, lefts[1:]))


def close(a, b):
    if a is None or b is None:
        return a is None and b is None
    return abs(a - b) <= TOL * max(1.0, abs(a), abs(b))


def near_list(a, b):
    return len(a) == len(b) and all(close(x, y) for x, y in zip(a, b))


def scope_check(phase, reading, smoke, failures):
    """The reading's slot set must be the registered one (or a prefix of it
    in smoke), and the phase's recorded step geometry must be the
    registration."""
    want = sorted("%s:%.6f" % (l, g) for l, g in census_slots(phase))
    have = sorted(reading["slots"])
    if smoke:
        if not set(have) <= set(want):
            failures.append(("<scope>", "smoke slots %s not in census" % have))
    elif have != want:
        failures.append(("<scope>", "%s vs registered %s" % (have, want)))
    if phase == "ultrafine":
        got = tuple(reading["steps"])
        if got != U_STEPS:
            failures.append(("<scope>", "steps %s vs %s" % (got, U_STEPS)))
    if phase == "stringdelta":
        if abs(reading["step"] - D_STEP) > 1e-12:
            failures.append(("<scope>", "step %s" % reading["step"]))
        got = tuple(reading["deltas"])
        if got != D_DELTAS and not (smoke and got
                                    and set(got) <= set(D_DELTAS)):
            failures.append(("<scope>", "deltas %s" % (reading["deltas"],)))
    if phase == "stringcensus":
        if tuple(reading["deltas"]) != S_DELTAS:
            failures.append(("<scope>", "deltas %s" % (reading["deltas"],)))
        if tuple(reading["scales"]) != S_SCALES:
            failures.append(("<scope>", "scales %s" % (reading["scales"],)))
    return want


def check_ultrafine(smoke):
    suffix = "_smoke" if smoke else ""
    rows = load(ROWS["ultrafine"] + suffix + ".json")["rows"]
    reading = load(READING["ultrafine"] + suffix + ".json")
    failures = []
    scope_check("ultrafine", reading, smoke, failures)
    for key, slot in sorted(reading["slots"].items()):
        layer, gk = slot["layer"], slot["gamma"]
        counts = {}
        for step in U_STEPS:
            gkey = "%g" % step
            blob = slot["grids"].get(gkey)
            if blob is None:
                failures.append((key, "grid %s missing" % gkey))
                continue
            cells = slice_rows(rows, layer, gk, reading["delta"],
                               grid(step, smoke))
            walk = pair_walk(cells, 1, step)
            if walk["n_pairs"] != blob["n_pairs"]:
                failures.append((key, "%s n_pairs %s vs %s"
                                 % (gkey, walk["n_pairs"], blob["n_pairs"])))
            for field in ("c_flip", "h_flip"):
                if walk[field] != blob[field]:
                    failures.append((key, "%s %s %s vs %s"
                                     % (gkey, field, walk[field],
                                        blob[field])))
            if len(cells) != blob["n_certified"]:
                failures.append((key, "%s n_certified %s vs %s"
                                 % (gkey, len(cells), blob["n_certified"])))
            rate = walk["c_rate"] = (walk["c_flip"] / walk["n_pairs"]
                                     if walk["n_pairs"] else None)
            if not close(rate, blob["c_rate"]):
                failures.append((key, "%s c_rate" % gkey))
            l = (step / rate) if rate else None
            if not close(l, blob["L"]):
                failures.append((key, "%s L %s vs %s" % (gkey, l, blob["L"])))
            no_flips = bool(walk["n_pairs"] and rate == 0.0)
            if no_flips != blob["no_flips"]:
                failures.append((key, "%s no_flips" % gkey))
            lefts = flip_lefts(cells, 1, step)
            if not near_list(lefts, blob["flip_lefts"]):
                failures.append((key, "%s flip_lefts %s vs %s"
                                 % (gkey, lefts, blob["flip_lefts"])))
            if not close(min_gap(lefts), blob["min_flip_gap"]):
                failures.append((key, "%s min_flip_gap %s vs %s"
                                 % (gkey, min_gap(lefts),
                                    blob["min_flip_gap"])))
            counts[gkey] = blob["c_flip"]
        gain = counts.get("0.001", 0) - counts.get("0.002", 0)
        if gain != slot["count_gain_001_002"]:
            failures.append((key, "count_gain_001_002 %s vs %s"
                             % (gain, slot["count_gain_001_002"])))
        gain5 = counts.get("0.001", 0) - counts.get("0.005", 0)
        if gain5 != slot["count_gain_001_005"]:
            failures.append((key, "count_gain_001_005 %s vs %s"
                             % (gain5, slot["count_gain_001_005"])))
        for a, b, name in ((slot["grids"]["0.001"]["L"],
                            slot["grids"]["0.002"]["L"], "ratio_001_002"),
                           (slot["grids"]["0.001"]["L"],
                            slot["grids"]["0.005"]["L"], "ratio_001_005")):
            ratio = max(a, b) / min(a, b) if a and b and a > 0 and b > 0 \
                else None
            if not close(ratio, slot[name]):
                failures.append((key, "%s %s vs %s" % (name, ratio,
                                                       slot[name])))
    verdict = "U-CONVERGED"
    if reading["instrument_fail"]:
        verdict = "U-INSTRUMENT-FAIL"
    elif any(s["count_gain_001_002"] > 0 for s in reading["slots"].values()):
        verdict = "U-UNRESOLVED"
    elif any(s["grids"]["0.001"]["c_flip"] == 0
             and s["grids"]["0.002"]["c_flip"] == 0
             for s in reading["slots"].values()):
        verdict = "U-DEGENERATE"
    if verdict != reading["verdict"]:
        failures.append(("<verdict>", "%s vs %s" % (verdict,
                                                    reading["verdict"])))
    return failures, verdict


def check_stringdelta(smoke):
    suffix = "_smoke" if smoke else ""
    rows = load(ROWS["stringdelta"] + suffix + ".json")["rows"]
    p1 = load("2024_ladder9_rows.json")["rows"]
    reading = load(READING["stringdelta"] + suffix + ".json")
    failures = []
    scope_check("stringdelta", reading, smoke, failures)
    scales = grid(D_STEP, smoke)
    for key, slot in sorted(reading["slots"].items()):
        layer, gk = slot["layer"], slot["gamma"]
        ref = sign_string(slice_rows(p1, layer, gk, D_REFERENCE, scales))
        if norm_str(ref) != norm_str(slot["reference"]["string"]):
            failures.append((key, "reference string differs"))
        if flips_of(ref, scales) != tuple(slot["reference"]["flips"]):
            failures.append((key, "reference flips %s vs %s"
                             % (flips_of(ref, scales),
                                slot["reference"]["flips"])))
        for dkey, blob in sorted(slot["deltas"].items()):
            delta = float(dkey)
            cells = slice_rows(rows, layer, gk, delta, scales)
            seq = sign_string(cells)
            k, n, only_ref, only_new = compare(ref, seq)
            if k != blob["disagreements"]:
                failures.append((key, "d=%s disagreements %s vs %s"
                                 % (dkey, k, blob["disagreements"])))
            if n != blob["n_common"]:
                failures.append((key, "d=%s n_common %s vs %s"
                                 % (dkey, n, blob["n_common"])))
            if len(ref) != blob["n_reference"]:
                failures.append((key, "d=%s n_reference" % dkey))
            if norm_list(only_ref) != norm_list(blob["only_reference"]):
                failures.append((key, "d=%s only_reference %s vs %s"
                                 % (dkey, only_ref,
                                    blob["only_reference"])))
            if norm_list(only_new) != norm_list(blob["only_new"]):
                failures.append((key, "d=%s only_new %s vs %s"
                                 % (dkey, only_new, blob["only_new"])))
            if flips_of(seq, scales) != tuple(blob["flips"]):
                failures.append((key, "d=%s flips %s vs %s"
                                 % (dkey, flips_of(seq, scales),
                                    blob["flips"])))
            if len(cells) != blob["n_certified"]:
                failures.append((key, "d=%s n_certified" % dkey))
            got = reading["slot_grids"][key]["deltas"][dkey]["string"]
            if norm_str(seq) != norm_str(got):
                failures.append((key, "d=%s stored string differs" % dkey))
    verdict = "STRING-DELTA-STABLE"
    if reading["instrument_fail"]:
        verdict = "STRING-DELTA-INSTRUMENT-FAIL"
    elif any(b["disagreements"] > 0 for s in reading["slots"].values()
             for b in s["deltas"].values()):
        verdict = "STRING-DELTA-BREAKS"
    elif any(b["n_common"] != b["n_reference"]
             for s in reading["slots"].values()
             for b in s["deltas"].values()):
        verdict = "STRING-DELTA-INCOMPLETE"
    if verdict != reading["verdict"]:
        failures.append(("<verdict>", "%s vs %s" % (verdict,
                                                    reading["verdict"])))
    return failures, verdict


def check_stringcensus(smoke):
    suffix = "_smoke" if smoke else ""
    rows = load(ROWS["stringcensus"] + suffix + ".json")["rows"]
    reading = load(READING["stringcensus"] + suffix + ".json")
    failures = []
    scope_check("stringcensus", reading, smoke, failures)
    for key, slot in sorted(reading["slots"].items()):
        layer, gk = slot["layer"], slot["gamma"]
        strings = {}
        for delta in S_DELTAS:
            strings["%.3f" % delta] = sign_string(
                slice_rows(rows, layer, gk, delta, S_SCALES))
        if norm_nested(strings) != norm_nested(slot["strings"]):
            failures.append((key, "strings differ"))
        first = "%.3f" % S_DELTAS[0]
        first_break = None
        for delta in S_DELTAS:
            dkey = "%.3f" % delta
            k, n, only_ref, only_new = compare(strings[first],
                                               strings[dkey])
            blob = slot["vs_first"][dkey]
            if k != blob["disagreements"] or n != blob["n_common"]:
                failures.append((key, "d=%s vs_first %s/%s vs %s/%s"
                                 % (dkey, k, n, blob["disagreements"],
                                    blob["n_common"])))
            if norm_list(only_ref) != norm_list(blob["only_reference"]):
                failures.append((key, "d=%s only_reference" % dkey))
            if norm_list(only_new) != norm_list(blob["only_new"]):
                failures.append((key, "d=%s only_new" % dkey))
            if k > 0 and first_break is None:
                first_break = delta
        if not close(first_break, slot["first_break_delta"]):
            failures.append((key, "first_break_delta %s vs %s"
                             % (first_break, slot["first_break_delta"])))
    verdict = "STRING-CENSUS-UNIFORM"
    if reading["instrument_fail"]:
        verdict = "STRING-CENSUS-INSTRUMENT-FAIL"
    elif any(b["n_common"] != len(S_SCALES)
             for s in reading["slots"].values()
             for b in s["vs_first"].values()):
        verdict = "STRING-CENSUS-INCOMPLETE"
    elif any(s["first_break_delta"] is not None
             for s in reading["slots"].values()):
        verdict = "STRING-CENSUS-BREAKS"
    if verdict != reading["verdict"]:
        failures.append(("<verdict>", "%s vs %s" % (verdict,
                                                    reading["verdict"])))
    return failures, verdict


def main():
    phase = sys.argv[1] if len(sys.argv) > 1 else ""
    smoke = "--smoke" in sys.argv
    if phase == "ultrafine":
        failures, verdict = check_ultrafine(smoke)
    elif phase == "stringdelta":
        failures, verdict = check_stringdelta(smoke)
    elif phase == "stringcensus":
        failures, verdict = check_stringcensus(smoke)
    else:
        raise SystemExit("usage: check_ladder_readings_2026.py "
                         "ultrafine|stringdelta|stringcensus [--smoke]")
    print("independent recomputation (%s%s): %d field failures"
          % (phase, " smoke" if smoke else "", len(failures)))
    for key, msg in failures:
        print("  FAIL %-24s %s" % (key, msg))
    print("verdict reproduced: %s" % verdict)
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
