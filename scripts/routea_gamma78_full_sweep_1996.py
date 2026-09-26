#!/usr/bin/env python3
# routea_gamma78_full_sweep_1996.py — record 1996 (pre-registered)
#
# Full committed rescue grid at gamma_7 / gamma_8 through the 1994 EXT
# layer, plus the 3 missing gamma_5@EXT knot cells. Decides between
# HOST_CONFIRMED / HEALTHY_NO_WIRE / HEIGHT_WALL per height, under the
# 1994 instrument law (n_primes > 4000 => Ap dropped => row is
# INSTRUMENT, never certifying).
#
# No gate-sign theorem, no determinant theorem, no RH claim.

import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import routea_opposite_gates_height_1994 as r94  # noqa: E402

G5 = r94.r80.GAMMAS[4]
G7 = r94.G7
G8 = r94.G8

SCALES = (0.86, 0.88, 0.90, 0.92, 0.94)
DELTAS = (0.10, 0.20, 0.30)
G5_EXTRA = (0.88, 0.90, 0.94)  # completes the 1994b knot map at delta=0.10


def certified(rec):
    """row_ok from 1994 PLUS the three-live-route requirement."""
    return r94.row_ok(rec) and rec["n_primes"] <= 4000 and \
        set(rec["routes"]) >= {"A", "Ap", "B"}


def verdict_for(rows):
    fin = [r for r in rows if r["density_finite"]]
    healthy = [r for r in fin if r["C"] > 0.0]
    wires = [r for r in healthy if certified(r) and r["D"] < 0.0
             and r["det"] < 0.0]
    if wires:
        return "HOST_CONFIRMED"
    if healthy:
        return "HEALTHY_NO_WIRE"
    return "HEIGHT_WALL"


def main():
    smoke = "--smoke" in sys.argv
    t0 = time.time()

    def stamp(msg):
        print("[%6.1fs] %s" % (time.time() - t0, msg), flush=True)

    stamp("record 1996 — gamma_7/8 full scale sweep (EXT)")
    cases = []
    if smoke:
        cases = [(0.10, G7, 0.90)]
    else:
        for d in DELTAS:
            for sc in SCALES:
                cases.append((d, G7, sc))
        for d in DELTAS:
            for sc in SCALES:
                cases.append((d, G8, sc))
        for sc in G5_EXTRA:
            cases.append((0.10, G5, sc))

    rows = []
    for (d, g, sc) in cases:
        tag = "G5MAP" if abs(g - G5) < 1e-9 else ("G7" if abs(g - G7) < 1e-9
                                                  else "G8")
        stamp("row d=%.2f g=%.4f sc=%.2f [%s]" % (d, g, sc, tag))
        rec = r94.run_row_ext(d, g, sc, 0)
        rec["tag"] = tag
        rows.append(rec)
        stamp("  np=%4d rt=%-5s | C=%+.4e b=%+.4e D=%+.4e det=%+.4e | "
              "sD=%.1e -> %s%s" % (
                  rec["n_primes"], "".join(rec["routes"]), rec["C"],
                  rec["B01"], rec["D"], rec["det"], rec["spread_D"],
                  rec["face"], "" if rec["n_primes"] <= 4000 else " INSTR"))

    g7_rows = [r for r in rows if r["tag"] == "G7"]
    g8_rows = [r for r in rows if r["tag"] == "G8"]
    g5_rows = [r for r in rows if r["tag"] == "G5MAP"]
    v7, v8 = verdict_for(g7_rows), verdict_for(g8_rows)
    stamp("=" * 96)
    stamp("gamma_5@EXT knot map (delta=0.10): %s" % " ".join(
        "sc=%.2f:C%+0.3g" % (r["scale"], r["C"]) for r in g5_rows))
    stamp("gamma_7: %s | gamma_8: %s" % (v7, v8))
    stamp("VERDICT: G7_%s+G8_%s" % (v7, v8))

    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..",
                       "results", "1996_gamma78_full_sweep.json")
    with open(out, "w", encoding="utf-8") as stream:
        stream.write(json.dumps({
            "record": "1996",
            "verdict": {"gamma_7": v7, "gamma_8": v8},
            "cases": rows,
        }, indent=2) + "\n")
    stamp("results -> %s" % os.path.abspath(out))


if __name__ == "__main__":
    main()
