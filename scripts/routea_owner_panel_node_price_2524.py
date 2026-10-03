"""2472: diagnostic price of the 2471 local node panels.

This is a 640-cell routing probe, not an integral certificate.  It asks one explicit
question: do the exact-owner coefficient balls and the 2471 half-step panel
geometry leave a plausible node price at the ten-cell grid?  The output is
kept separate from certified artifacts; no verdict may use it as a bound.
"""
import json
import hashlib
import sys
from fractions import Fraction
from pathlib import Path
import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
REPAIR = ROOT / "results/2338_exact_interpolation_repair.json"
CAPTURE = ROOT / "results/2275_gap_owner_audit.json"
OUT = ROOT / "results/2524_owner_panel_node_price.json"
mp.mp.dps = 100


def q(s):
    a, b = s.split("/") if "/" in s else (s, "1")
    return mp.mpf(a) / mp.mpf(b)


def interval_mul(a, b):
    v = [a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1]]
    return min(v), max(v)


def interval_add(a, b):
    return a[0] + b[0], a[1] + b[1]


def interval_sub(a, b):
    return a[0] - b[1], a[1] - b[0]


def rect_mul(a, b):
    ar, ai = a[0], a[1]
    br, bi = b[0], b[1]
    return (interval_sub(interval_mul(ar, br), interval_mul(ai, bi)),
            interval_add(interval_mul(ar, bi), interval_mul(ai, br)))


def main():
    repair = json.loads(REPAIR.read_text())
    capture = json.loads(CAPTURE.read_text())["owner_capture"]
    fam = []
    for row, pair in zip(repair["coefficient_rows"], capture["families_hex"]):
        re_lo = q(row["ideal_base_coefficient"]["real"]["lower_exact"])
        re_hi = q(row["ideal_base_coefficient"]["real"]["upper_exact"])
        im_lo = q(row["ideal_base_coefficient"]["imag"]["lower_exact"])
        im_hi = q(row["ideal_base_coefficient"]["imag"]["upper_exact"])
        fam.append({
            "rad": mp.mpf(float.fromhex(pair[0])) ** 2,
            "mod": mp.mpf(float.fromhex(pair[1])),
            "re": (re_lo, re_hi), "im": (im_lo, im_hi),
            "coef_norm": mp.sqrt(((re_lo + re_hi) / 2) ** 2 +
                                  ((im_lo + im_hi) / 2) ** 2),
        })
    radius = mp.mpf(2076918743413931858457251756481) / mp.mpf(
        316912650057057350374175801344)
    cells = int(sys.argv[1]) if len(sys.argv) > 1 else 640
    step = 2 * radius / cells
    rows = []
    for index in range(cells + 1):
        x = -radius + index * step
        x0, x1 = x - step / 2, x + step / 2
        rect = ((mp.mpf("0"), mp.mpf("0")), (mp.mpf("0"), mp.mpf("0")))
        for f in fam:
            if x0 >= 0:
                if x0 < f["rad"]:
                    bump_hi = mp.exp(-30 / (1 - (x0 / f["rad"]) ** 2))
                else:
                    bump_hi = mp.mpf("0")
            elif x1 <= 0:
                if -f["rad"] < x1:
                    bump_hi = mp.exp(-30 / (1 - (x1 / f["rad"]) ** 2))
                else:
                    bump_hi = mp.mpf("0")
            else:
                bump_hi = mp.exp(-30)
            mid = f["mod"] * (x0 + x1) / 2
            rho = abs(f["mod"]) * (x1 - x0) / 2
            phase = ((mp.cos(mid) - rho, mp.cos(mid) + rho),
                     (mp.sin(mid) - rho, mp.sin(mid) + rho))
            term = rect_mul(rect_mul((f["re"], f["im"]),
                                     ((mp.mpf("0"), bump_hi),
                                      (mp.mpf("0"), mp.mpf("0")))), phase)
            rect = (interval_add(rect[0], term[0]), interval_add(rect[1], term[1]))
        norm = max(abs(rect[0][0]), abs(rect[0][1])) + max(abs(rect[1][0]), abs(rect[1][1]))
        weighted = {str(s): mp.exp(mp.mpf(s) * x) * norm for s in ("-0.5", "0.5")}
        rows.append({"index": index, "x": mp.nstr(x, 30),
                     "norm_box": mp.nstr(norm, 30),
                     "weighted": {k: mp.nstr(v, 30) for k, v in weighted.items()}})
    composite = {}
    for s in ("-0.5", "0.5"):
        composite[s] = sum(
            step / 2 * (mp.mpf(rows[i]["weighted"][s]) +
                        mp.mpf(rows[i + 1]["weighted"][s]))
            for i in range(cells))
    constants = [1, 60, 3720, 236160, 15130080]
    budgets = {}
    for order in range(3):
        total = mp.mpf("0")
        for f in fam:
            for k in range(order + 1):
                choose = mp.binomial(order, k)
                total += f["coef_norm"] * choose * abs(f["mod"]) ** k * \
                    constants[order - k] * mp.exp(-30) / f["rad"] ** (order - k)
        budgets[str(order)] = total
    payload = {
        "record": 2524,
        "owner_radius": mp.nstr(radius, 50),
        "cells": cells,
        "step": mp.nstr(step, 50),
        "rows": rows,
        "composite_node_upper": {s: mp.nstr(v, 50) for s, v in composite.items()},
        "owner_derivative_budget_diagnostic": {k: mp.nstr(v, 50)
                                                for k, v in budgets.items()},
        "status": "DIAGNOSTIC_640_CELL_NOT_A_CERTIFICATE",
        "repair_sha256": hashlib.sha256(REPAIR.read_bytes()).hexdigest(),
        "capture_sha256": hashlib.sha256(CAPTURE.read_bytes()).hexdigest(),
    }
    OUT.write_text(json.dumps(payload, indent=2) + "\n")
    print("record=2524 status=DIAGNOSTIC_640_CELL_NOT_A_CERTIFICATE")
    print("max weighted node prices:",
          {s: max(mp.mpf(row["weighted"][s]) for row in rows) for s in ("-0.5", "0.5")})
    print("composite node prices:", {s: mp.nstr(v, 30) for s, v in composite.items()})
    print("derivative budget diagnostics:", {k: mp.nstr(v, 30) for k, v in budgets.items()})
    print("artifact:", OUT)


if __name__ == "__main__":
    main()
