#!/usr/bin/env python3
# fourpoint_refine_1982.py — record 1982 (interval-certification target)
#
# dxi-refinement of the record-1981 GO_CANDIDATE registered point
# (delta = 0.10, scale 1.0, n = 0): the certified-pair D reading must be
# bit-stable / dxi^4-convergent for an interval bracket to be worth cutting.
# This measures the bracket TARGET width before the Lean interval work.

import json
import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import fourpoint_owner_density_1959 as r59   # noqa: E402
import fourpoint_offline_owner_1981 as r81   # noqa: E402

T0 = time.time()


def log(msg):
    print("[%7.1fs] %s" % (time.time() - T0, msg), flush=True)


def main():
    rows = []
    for dxi in (0.008, 0.004, 0.002, 0.001, 0.0005):
        rec = r81.run_case(0.10, 1.0, 0, xi_max=8.0, dxi=dxi)
        rows.append({"dxi": dxi, "D": rec["D"], "C": rec["C"],
                     "B01": rec["B01"], "spread_D": rec["spread_D"],
                     "routes": rec["routes"]})
        log("dxi %.4f : D = %+.10e (spread %.1e)" % (dxi, rec["D"],
                                                     rec["spread_D"]))
    stable = len(set(round(r["D"], 9) for r in rows)) <= 2
    report = {
        "record": 1982,
        "status": "REFINE_TARGET",
        "point": "delta=0.10 scale=1.0 n=0, xi_max=8",
        "all_bit_stable_9dp": stable,
        "rows": rows,
    }
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..",
                       "results", "1982_refine_target.json")
    with open(out, "w", encoding="utf-8") as stream:
        stream.write(json.dumps(report, indent=2) + "\n")
    log("bit-stable at 9dp across dxi: %s" % stable)
    log("wrote %s" % os.path.abspath(out))


if __name__ == "__main__":
    main()
