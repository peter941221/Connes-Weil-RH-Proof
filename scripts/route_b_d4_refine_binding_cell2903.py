"""Probe local angular refinement of the binding Route-B Cauchy cell."""
import hashlib
import json
from pathlib import Path
import sys

from mpmath import iv

sys.path.insert(0, str(Path(__file__).parent))
import route_b_d4_cauchy_interval2889 as base


def max_upper(cells):
    radius = iv.mpf("0.05")
    maximum = iv.mpf("0")
    argmax = None
    for k in range(cells):
        theta = iv.mpf([
            2 * 3.141592653589793 * k / cells,
            2 * 3.141592653589793 * (k + 1) / cells,
        ])
        t = radius * (iv.cos(theta) + 1j * iv.sin(theta))
        upper = base.abs_upper(base.h_of(t, base.z_of(t)))
        if upper > maximum:
            maximum, argmax = upper, k
    return str(maximum), argmax


def main():
    rows = []
    for cells in (256, 512, 1024, 2048):
        upper, argmax = max_upper(cells)
        rows.append({"angle_cells": cells, "upper": upper, "argmax": argmax})
    payload = {
        "record": 2903,
        "binding_cell": 214,
        "rows": rows,
        "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "claims": {
            "refinement_probe": True,
            "formal_interval_soundness": False,
            "full_cauchy_certificate": False,
        },
        "decision": "refine binding cell before expanding Lean interval wrappers",
    }
    out = Path("results/2903_route_b_d4_refine_binding_cell.json")
    out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
