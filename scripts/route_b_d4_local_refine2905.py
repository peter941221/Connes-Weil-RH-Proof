"""Refine the binding 256-cell into local angular subcells."""
import hashlib
import json
from pathlib import Path
import sys
from mpmath import iv

sys.path.insert(0, str(Path(__file__).parent))
import route_b_d4_cauchy_interval2889 as base


def base_rect(value):
    return {
        "re_lo": base.endpoint_text(value.real.a),
        "re_hi": base.endpoint_text(value.real.b),
        "im_lo": base.endpoint_text(value.imag.a),
        "im_hi": base.endpoint_text(value.imag.b),
    }


def main():
    parent_cells, parent = 256, 214
    subdivisions = 8
    radius = iv.mpf("0.05")
    lo = 2 * 3.141592653589793 * parent / parent_cells
    hi = 2 * 3.141592653589793 * (parent + 1) / parent_cells
    rows = []
    stages = None
    for j in range(subdivisions):
        a = lo + (hi - lo) * j / subdivisions
        b = lo + (hi - lo) * (j + 1) / subdivisions
        theta = iv.mpf([a, b])
        t = radius * (iv.cos(theta) + 1j * iv.sin(theta))
        value = base.h_of(t, base.z_of(t))
        if j == 0:
            a_value = 2 * t / (1 - t * t)
            e_value = iv.exp(2 * a_value)
            z_value = (e_value - 1) / (e_value + 1) / t
            stages = {
                "t": base_rect(t),
                "a": base_rect(a_value),
                "exp2a": base_rect(e_value),
                "z": base_rect(z_value),
                "H": base_rect(value),
            }
        rows.append({
            "subcell": j,
            "theta_lo": repr(a),
            "theta_hi": repr(b),
            "re_lo": base.endpoint_text(value.real.a),
            "re_hi": base.endpoint_text(value.real.b),
            "im_lo": base.endpoint_text(value.imag.a),
            "im_hi": base.endpoint_text(value.imag.b),
            "upper": str(base.abs_upper(value)),
        })
    payload = {
        "record": 2905,
        "parent_cells": parent_cells,
        "parent_cell": parent,
        "subdivisions": subdivisions,
        "rows": rows,
        "stages_subcell_0": stages,
        "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "claims": {"local_refinement_probe": True,
                    "formal_interval_soundness": False},
    }
    out = Path("results/2905_route_b_d4_local_refine.json")
    out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
