"""2477: interval-structure smoke for the 2475 local curvature premise.

This uses mpmath.iv only as an interval-structure smoke.  The project-grade
promotion target remains Arb/MPFR (and eventually a Lean literal import).
The edge fallback uses the already-proved global bump constants when a cell
touches a support edge; it prevents the naive interval 0/0 explosion.
"""
import json
import math
import subprocess
import sys
from pathlib import Path

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
REPAIR = ROOT / "results/2338_exact_interpolation_repair.json"
CAPTURE = ROOT / "results/2275_gap_owner_audit.json"
OUT = ROOT / "results/2477_owner_local_curvature_iv.json"
mp.iv.dps = 80


def frac(s):
    p = s.split("/")
    return mp.mpf(p[0]) / mp.mpf(p[1]) if len(p) == 2 else mp.mpf(p[0])


def hi(x):
    return float(x.b)


def bump_bound_iv(order, rad, xlo, xhi, step):
    # Global ladder constant is a valid fallback at a support edge.
    constants = (1, 60, 3720)
    global_bound = mp.iv.mpf(constants[order]) * mp.iv.exp(-30) / rad ** order
    lo = max(xlo, -float(rad) + step / 1000)
    high = min(xhi, float(rad) - step / 1000)
    if lo >= high:
        return global_bound, "edge-global"
    x = mp.iv.mpf([lo, high]) / rad
    d = 1 - x ** 2
    if order == 0:
        p = mp.iv.mpf(1)
    elif order == 1:
        p = -60 * x
    else:
        p = -60 + 3480 * x ** 2 + 180 * x ** 4
    core = mp.iv.exp(-30 / d) * abs(p) / (d ** (2 * order) * rad ** order)
    # The max with the global edge fallback covers the removed slivers.
    return mp.iv.mpf([0, max(hi(core), hi(global_bound))]), "core+edge"


def main():
    cells = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    subdiv = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    repair = json.loads(REPAIR.read_text())
    capture = json.loads(CAPTURE.read_text())["owner_capture"]
    fam = []
    for row, pair in zip(repair["coefficient_rows"], capture["families_hex"]):
        re = (frac(row["ideal_base_coefficient"]["real"]["lower_exact"]) +
              frac(row["ideal_base_coefficient"]["real"]["upper_exact"])) / 2
        im = (frac(row["ideal_base_coefficient"]["imag"]["lower_exact"]) +
              frac(row["ideal_base_coefficient"]["imag"]["upper_exact"])) / 2
        fam.append((mp.sqrt(re ** 2 + im ** 2),
                    mp.mpf(float.fromhex(pair[0])) ** 2,
                    mp.mpf(float.fromhex(pair[1]))))
    radius = mp.mpf(2076918743413931858457251756481) / mp.mpf(
        316912650057057350374175801344)
    step = float(2 * radius / cells)
    substep = step / subdiv
    rows = []
    edge_modes = set()
    for sigma in (-mp.mpf("0.5"), mp.mpf("0.5")):
        values = []
        for index in range(cells * subdiv):
            left = float(-radius + index * substep)
            right = float(-radius + (index + 1) * substep)
            total = mp.iv.mpf(0)
            for coef, rad, mod in fam:
                bump = [bump_bound_iv(order, rad, left, right, substep)
                        for order in range(3)]
                edge_modes.update(mode for _, mode in bump)
                ext = []
                for order in range(3):
                    val = mp.iv.mpf(0)
                    for j in range(order + 1):
                        val += (mp.iv.mpf(math.comb(order, j)) *
                                mp.iv.mpf(abs(mod)) ** j * bump[order - j][0])
                    ext.append(val)
                weighted = (ext[2] + 2 * mp.iv.mpf(abs(sigma)) * ext[1] +
                            mp.iv.mpf(sigma) ** 2 * ext[0])
                x = mp.iv.mpf([left, right])
                total += mp.iv.mpf(coef) * mp.iv.exp(mp.iv.mpf(sigma) * x) * weighted
            values.append(hi(total))
        rows.append({"sigma": str(sigma), "max_cell": max(values),
                     "binding_index": values.index(max(values)),
                     "remainder": substep ** 3 / 12 * sum(values),
                     "cells": cells, "subdiv": subdiv,
                     "effective_cells": cells * subdiv})
    result = {"record": 2477,
              "status": "MPMATH_IV_STRUCTURE_SMOKE_NOT_PROJECT_CERTIFICATE",
              "cells": cells, "subdiv": subdiv,
              "effective_cells": cells * subdiv, "step": substep, "rows": rows,
              "edge_modes": sorted(edge_modes),
              "nonclaims": ["not Arb/MPFR", "not Lean literal", "no producer GO", "no RH"]}
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
