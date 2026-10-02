"""2478: project-MPFR directed smoke for the 2475 local curvature array.

This reuses the repository's 256-bit libmpfr wrapper from 2286/2445 and the
2477 edge-split/subcell structure.  It is still not a Lean numeric import:
the final artifact is a backend smoke until its exact owner-rational binding
and independent pin are added.
"""
import hashlib
import importlib.util
import json
import math
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPAIR = ROOT / "results/2338_exact_interpolation_repair.json"
CAPTURE = ROOT / "results/2275_gap_owner_audit.json"
OUT = ROOT / "results/2478_owner_local_curvature_mpfr.json"

spec = importlib.util.spec_from_file_location(
    "routea_mpfr_2286", ROOT / "scripts/routea_mpfr_owner_atom_preflight_2286.py")
mpfr = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mpfr)


def frac(s):
    p = s.split("/")
    return float(p[0]) / float(p[1]) if len(p) == 2 else float(p[0])


def outward(v):
    v = float(v)
    return math.nextafter(v, -math.inf), math.nextafter(v, math.inf)


def abs_iv(x):
    return (0.0, max(abs(x[0]), abs(x[1])))


def bump_bound(order, rad, left, right, step):
    constants = (1, 60, 3720)
    global_bound = mpfr.mul(outward(constants[order]),
                            mpfr.div(outward(math.exp(-30)), outward(rad ** order)))
    lo = max(left, -rad + step / 1000)
    hi = min(right, rad - step / 1000)
    if lo >= hi:
        return global_bound, "edge-global"
    x = outward((lo + hi) / 2)
    x = (outward(lo)[0], outward(hi)[1])
    t = mpfr.div(x, outward(rad))
    d = mpfr.sub(outward(1.0), mpfr.mul(t, t))
    if d[0] <= 0:
        return global_bound, "edge-global"
    if order == 0:
        p = outward(1.0)
    elif order == 1:
        p = mpfr.mul(outward(-60.0), t)
    else:
        t2 = mpfr.mul(t, t)
        t4 = mpfr.mul(t2, t2)
        p = mpfr.add(mpfr.add(outward(-60.0), mpfr.mul(outward(3480.0), t2)),
                     mpfr.mul(outward(180.0), t4))
    d2 = mpfr.mul(d, d)
    d2q = (1.0, 1.0) if order == 0 else d2
    if order == 2:
        d2q = mpfr.mul(d2, d2)
    value = mpfr.div(mpfr.mul(mpfr.unary("mpfr_exp", mpfr.div(outward(-30.0), d)),
                              abs_iv(p)),
                     mpfr.mul(d2q, outward(rad ** order)))
    return (min(value[0], global_bound[0]), max(value[1], global_bound[1])), "core+edge"


def main():
    cells = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    subdiv = int(sys.argv[2]) if len(sys.argv) > 2 else 16
    repair = json.loads(REPAIR.read_text())
    capture = json.loads(CAPTURE.read_text())["owner_capture"]
    fam = []
    for row, pair in zip(repair["coefficient_rows"], capture["families_hex"]):
        re = (frac(row["ideal_base_coefficient"]["real"]["lower_exact"]) +
              frac(row["ideal_base_coefficient"]["real"]["upper_exact"])) / 2
        im = (frac(row["ideal_base_coefficient"]["imag"]["lower_exact"]) +
              frac(row["ideal_base_coefficient"]["imag"]["upper_exact"])) / 2
        # Outward float norm is a temporary binding; exact rational norm is
        # the required next pin step.
        coef = outward(math.hypot(re, im))[1]
        fam.append((coef, float.fromhex(pair[0]) ** 2, float.fromhex(pair[1])))
    radius = 2076918743413931858457251756481 / 316912650057057350374175801344
    step = 2 * radius / cells
    substep = step / subdiv
    rows, modes = [], set()
    for sigma in (-0.5, 0.5):
        values = []
        for index in range(cells * subdiv):
            left, right = -radius + index * substep, -radius + (index + 1) * substep
            total = 0.0
            for coef, rad, mod in fam:
                bump = [bump_bound(order, rad, left, right, substep)
                        for order in range(3)]
                modes.update(mode for _, mode in bump)
                ext = []
                for order in range(3):
                    value = (0.0, 0.0)
                    for j in range(order + 1):
                        term = mpfr.mul(outward(math.comb(order, j) * abs(mod) ** j),
                                        bump[order - j][0])
                        value = mpfr.add(value, term)
                    ext.append(value)
                weighted = mpfr.add(ext[2], mpfr.add(
                    mpfr.mul(outward(2 * abs(sigma)), ext[1]),
                    mpfr.mul(outward(sigma ** 2), ext[0])))
                weight = mpfr.unary("mpfr_exp", mpfr.mul(outward(sigma),
                                                          (outward(left)[0], outward(right)[1])))
                total += coef * mpfr.mul(weight, weighted)[1]
            values.append(total)
        rows.append({"sigma": sigma, "max_cell": max(values),
                     "binding_index": values.index(max(values)),
                     "remainder": substep ** 3 / 12 * sum(values),
                     "cells": cells, "subdiv": subdiv,
                     "effective_cells": cells * subdiv})
    result = {
        "record": 2478,
        "status": "PROJECT_MPFR_DIRECTED_SMOKE_NOT_LEAN_CERTIFICATE",
        "backend": {"library": "libmpfr.so.6", "precision_bits": mpfr.PREC,
                    "rounding": "RNDD/RNDU"},
        "cells": cells, "subdiv": subdiv, "step": substep, "rows": rows,
        "edge_modes": sorted(modes),
        "repair_sha256": hashlib.sha256(REPAIR.read_bytes()).hexdigest(),
        "capture_sha256": hashlib.sha256(CAPTURE.read_bytes()).hexdigest(),
        "nonclaims": ["temporary float binding of exact coefficient norm",
                       "no Lean literal import", "no producer GO", "no RH"],
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
