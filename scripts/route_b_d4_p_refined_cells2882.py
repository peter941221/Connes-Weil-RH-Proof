"""Refine the owner-correlated P interval screen and locate undecided cells."""
import json
from pathlib import Path
import runpy
import mpmath as mp

base = runpy.run_path("scripts/route_b_d4_p_interval_cells2881.py")
z_of = base["z_of"]
p_interval = base["p_interval"]


def main():
    mp.iv.dps = 40
    regions = [(mp.mpf(1) / 4096, mp.mpf("0.1353"), "negative"),
               (mp.mpf("0.3029"), mp.mpf("0.4999"), "positive")]
    cells = 2000
    rows = []
    for left, right, expected in regions:
        t0, t1 = 2 * left - 1, 2 * right - 1
        undecided = []
        for k in range(cells):
            a = t0 + (t1 - t0) * k / cells
            b = t0 + (t1 - t0) * (k + 1) / cells
            value = p_interval(a, b, z_of(a), z_of(b))
            ok = value.b < 0 if expected == "negative" else value.a > 0
            if not ok:
                undecided.append(k)
        rows.append({"u_left": str(left), "u_right": str(right),
                     "expected_sign": expected, "cells": cells,
                     "certified": cells - len(undecided),
                     "undecided_count": len(undecided),
                     "undecided_first": undecided[:10],
                     "undecided_last": undecided[-10:]})
    payload = {"record": 2882, "rows": rows,
               "claims": {"refined_outward_screen": True,
                          "global_sign_certificate": False},
               "decision": "focus Taylor endpoint cells; interior cells are interval-certified"}
    out = Path("results/2882_route_b_d4_p_refined_cells.json")
    out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
