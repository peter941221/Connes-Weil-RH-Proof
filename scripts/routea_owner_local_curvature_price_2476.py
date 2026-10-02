"""2476: sampled price for the actual-owner cell-local curvature premise.

The bump derivative formulas are the same order-0/1/2 ladder used by the
Lean budget.  Each cell is sampled in its own normalized coordinate and the
family sum is kept before the final scalar charge.  This is explicitly a
feasibility probe: sampled maxima and binary64 arithmetic are not a uniform
interval enclosure and cannot discharge 2475.
"""
import json
import math
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
REPAIR = ROOT / "results/2338_exact_interpolation_repair.json"
CAPTURE = ROOT / "results/2275_gap_owner_audit.json"
OUT = ROOT / "results/2476_owner_local_curvature_price.json"


def frac(s):
    p = s.split("/")
    return float(p[0]) / float(p[1]) if len(p) == 2 else float(p[0])


def main():
    cells = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    samples = int(sys.argv[2]) if len(sys.argv) > 2 else 401
    repair = json.loads(REPAIR.read_text())
    capture = json.loads(CAPTURE.read_text())["owner_capture"]
    coeff = []
    fam = []
    for row, pair in zip(repair["coefficient_rows"], capture["families_hex"]):
        re = (frac(row["ideal_base_coefficient"]["real"]["lower_exact"]) +
              frac(row["ideal_base_coefficient"]["real"]["upper_exact"])) / 2
        im = (frac(row["ideal_base_coefficient"]["imag"]["lower_exact"]) +
              frac(row["ideal_base_coefficient"]["imag"]["upper_exact"])) / 2
        coeff.append(math.hypot(re, im))
        fam.append((float.fromhex(pair[0]) ** 2, float.fromhex(pair[1])))
    radius = 2076918743413931858457251756481 / 316912650057057350374175801344
    step = 2 * radius / cells
    constants = (1.0, 60.0, 3720.0)
    rows = []
    for sigma in (-0.5, 0.5):
        local = []
        for i in range(cells):
            left, right = -radius + i * step, -radius + (i + 1) * step
            x = np.linspace(left, right, samples)
            total = 0.0
            for c, (rad, mod) in zip(coeff, fam):
                inside = np.abs(x) < rad
                t = np.divide(x, rad, out=np.zeros_like(x), where=inside)
                d = 1.0 - t * t
                e = np.where(inside, np.exp(-30.0 / np.maximum(d, 1e-300)), 0.0)
                p = (np.ones_like(x), -60.0 * t,
                     -60.0 + 3480.0 * t * t + 180.0 * t ** 4)
                bump = tuple(np.where(inside,
                                      e * np.abs(p[q]) /
                                      (np.maximum(d, 1e-300) ** (2 * q) * rad ** q),
                                      0.0) for q in range(3))
                ext = []
                for order in range(3):
                    ext.append(sum(math.comb(order, j) * abs(mod) ** j *
                                   bump[order - j] for j in range(order + 1)))
                weighted = (ext[2] + 2 * abs(sigma) * ext[1] +
                            sigma * sigma * ext[0])
                total += c * float(np.max(np.exp(sigma * x) * weighted))
            local.append(total)
        remainder = step ** 3 / 12 * sum(local)
        rows.append({"sigma": sigma, "max_cell": max(local),
                     "remainder": remainder, "cells": cells,
                     "samples_per_cell": samples})
    result = {
        "record": 2476,
        "status": "SAMPLED_FEASIBILITY_PROBE_NOT_A_CERTIFICATE",
        "radius": radius, "step": step, "rows": rows,
        "decision": "local_price_only; directed_cell_enclosure_required",
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
