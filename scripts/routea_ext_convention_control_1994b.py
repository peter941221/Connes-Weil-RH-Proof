#!/usr/bin/env python3
# routea_ext_convention_control_1994b.py — record 1994 post-hoc control
#
# NOT part of the pre-registered case set. This control disambiguates the
# 1994 height-extension anomaly (gamma_7/gamma_8 read C << 0, D < 0,
# det > 0 on the 17-node 10-ordinate owner) between two confounded causes:
#
#   (i)  the height itself (37.6/40.9 vs the committed <= 32.9 ordinates);
#   (ii) the convention change (kill list 6 -> 10 ordinates, M 13 -> 17,
#        kill width pool -> 5.4, support radius -> 10.8, visible primes
#        231 -> 5121).
#
# Control: re-measure gamma_5 (delta = 0.10) through the SAME EXT layer
# used for gamma_7/gamma_8.  If gamma_5@EXT also reads C << 0 with
# det > 0, the collapse is the CONVENTION, not the height; if gamma_5@EXT
# reads like the committed gamma_5 rows (C > 0), the collapse is genuinely
# height-driven.  Labels are fixed here before the run:
#
#   CONVENTION_ARTIFACT : gamma_5@EXT reads C < 0 at BOTH sc in {0.86, 0.92}
#   HEIGHT_EFFECT       : gamma_5@EXT reads C > 0 at BOTH sc in {0.86, 0.92}
#   MIXED               : anything else
#
# No gate-sign theorem, no determinant theorem, no RH claim.

import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import routea_opposite_gates_height_1994 as r94  # noqa: E402

G5 = r94.r80.GAMMAS[4]


def main():
    print("[control] gamma_5 through the EXT layer (10-ordinate kills)", flush=True)
    rows = []
    for sc in (0.86, 0.92, 1.00):
        rows.append(r94.run_row_ext(0.10, G5, sc, 0, dxi=0.004))
    cvals = {r["scale"]: r["C"] for r in rows}
    neg = [sc for sc in (0.86, 0.92) if cvals[sc] < 0.0]
    pos = [sc for sc in (0.86, 0.92) if cvals[sc] > 0.0]
    if len(neg) == 2:
        label = "CONVENTION_ARTIFACT"
    elif len(pos) == 2:
        label = "HEIGHT_EFFECT"
    else:
        label = "MIXED"
    print("[control] C@0.86=%+.4e C@0.92=%+.4e C@1.00=%+.4e -> %s"
          % (cvals[0.86], cvals[0.92], cvals[1.00], label), flush=True)
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..",
                       "results", "1994b_ext_convention_control.json")
    with open(out, "w", encoding="utf-8") as stream:
        stream.write(json.dumps({
            "record": "1994b", "label": label,
            "purpose": "post-hoc control: EXT-convention vs height for the "
                       "gamma_7/gamma_8 det>0 anomaly",
            "cases": rows,
        }, indent=2) + "\n")
    print("[control] results -> %s" % os.path.abspath(out), flush=True)


if __name__ == "__main__":
    main()
