"""Record 2211: exponent-argument transcendental allowance price."""
import importlib.util
import json
import os
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
sp = importlib.util.spec_from_file_location(
    "full2206", ROOT / "scripts" / "routea_weighted_zero_vector_split_full_refinement_2206.py")
m = importlib.util.module_from_spec(sp)
sp.loader.exec_module(m)

OUT = ROOT / "results" / "2211_weighted_zero_transcendental_allowance.json"
U = np.finfo(float).eps / 2.0
NODE = 2
NSEG = 1100


def main():
    nodes, fam, A0, _bb, b_corr = m.v.r.matrices(m.v.r.M_REF)
    coeff = np.linalg.solve(A0, b_corr)
    xw = [m.v.q.r.r59.phi_weights(a, panels=6, m=m.M) for a, _ in fam]
    gl_abs = 0.0
    sim_abs = 0.0
    exp_smear = 0.0
    term_count = 0
    for c, (a, theta), (X, W) in zip(coeff, fam, xw):
        z = a * (nodes[NODE] + 1j * theta)
        f = np.exp(-m.v.q.r.K / (1.0 - (X / a) ** 2) + z * X)
        gl_abs += abs(c) * float(np.sum(np.abs(W * f)))
        term_count += len(X)
        lo_all, hi_all = -a * (1.0 - m.DELTA), a * (1.0 - m.DELTA)
        sim_local = 0.0
        for panel in range(m.NPAN):
            lo = lo_all + (hi_all - lo_all) * panel / m.NPAN
            hi = lo_all + (hi_all - lo_all) * (panel + 1) / m.NPAN
            xx = np.linspace(lo, hi, 2 * NSEG + 1)
            ff = np.exp(-m.v.q.r.K / (1.0 - (xx / a) ** 2) + z * xx)
            hh = (hi - lo) / (2 * NSEG)
            weights = np.ones(len(xx))
            weights[1:-1:2] = 4.0
            weights[2:-1:2] = 2.0
            sim_local += float(hh / 3.0 * np.sum(weights * np.abs(ff)))
            term_count += len(xx)
        sim_abs += abs(c) * sim_local
        amp = 8.0 * U * abs(z) * a
        exp_smear += abs(c) * amp * (
            float(np.sum(np.abs(W * f))) + sim_local)
    operation = 16.0 * U * (gl_abs + sim_abs)
    result = {
        "record": 2211,
        "status": "VECTOR-SPLIT-TRANSCENDENTAL-ALLOWANCE-PRICE",
        "node": NODE, "rhs": "correction", "NSEG": NSEG,
        "unit_roundoff": U, "term_count": term_count,
        "absolute_sums": {"gl": gl_abs, "simpson": sim_abs},
        "allowances": {
            "exp_argument_smear": exp_smear,
            "exp_term_operation": operation,
            "total": exp_smear + operation,
        },
        "reference": {
            "vector_bound_2209": 4.934893138128475e-5,
            "rounding_allowance_2210": 1.3176797747730188e-5,
            "combined_with_transcendental":
                4.934893138128475e-5 + 1.3176797747730188e-5 +
                exp_smear + operation,
        },
        "nonclaims": [
            "AMP is a forward-error price, not an interval proof of exp",
            "stored float sums and coefficients are not outward intervals",
            "no complete-owner transfer and no RH claim",
        ],
        "provenance": {
            "script": os.fspath(Path(__file__).relative_to(ROOT)),
            "parent": "scripts/routea_weighted_zero_vector_split_full_refinement_2206.py",
        },
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()

