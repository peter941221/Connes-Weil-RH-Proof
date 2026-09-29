"""Record 2203: matrix-level cancellation preflight.

This compares the same m=3200 -> m=6400 interpolation matrix difference as
2201, but does not take entrywise absolute values before applying it to the
actual base/correction solve vectors. It prices whether matrix-level
cancellation can avoid the 2202 entrywise no-go. This remains a measured
preflight, not an outward certificate.
"""
import importlib.util
import json
import os
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
spec = importlib.util.spec_from_file_location(
    "r2201", ROOT / "scripts" /
    "routea_weighted_zero_solve_enclosure_preflight_2201.py")
r = importlib.util.module_from_spec(spec)
spec.loader.exec_module(r)

OUT = ROOT / "results" / "2203_weighted_zero_matrix_cancellation_preflight.json"


def main():
    _nodes, _fam, A0, b_base, b_corr = r.matrices(r.M_REF)
    _nodes, _fam, A1, _bb, _bc = r.matrices(r.M_LOW)
    D = A1 - A0
    inv0 = np.linalg.inv(A0)
    rows = []
    for name, b in (("base", b_base), ("correction", b_corr)):
        c0 = np.linalg.solve(A0, b)
        action = D @ c0
        propagated = inv0 @ action
        direct_delta = c0 - np.linalg.solve(A1, b)
        rows.append({
            "rhs": name,
            "c0_inf": float(np.max(np.abs(c0))),
            "matrix_inf": float(np.max(np.sum(np.abs(D), axis=1))),
            "action_inf": float(np.max(np.abs(action))),
            "propagated_inf": float(np.max(np.abs(propagated))),
            "direct_solve_delta_inf": float(np.max(np.abs(direct_delta))),
            "cancellation_factor_matrix_over_action":
                float(np.max(np.sum(np.abs(D), axis=1)) /
                      max(np.max(np.abs(action)), np.finfo(float).tiny)),
        })
    result = {
        "record": 2203,
        "status": "MATRIX-LEVEL-CANCELLATION-PREFLIGHT",
        "matrix": {
            "reference_m": r.M_REF,
            "comparison_m": r.M_LOW,
            "dimension": int(A0.shape[0]),
            "condition": float(np.linalg.cond(A0)),
            "entrywise_inf": float(np.max(np.sum(np.abs(D), axis=1))),
        },
        "rhs_rows": rows,
        "nonclaims": [
            "matrix difference is not an analytic outward enclosure",
            "all values use stored floating quadrature chains",
            "no complete-owner transfer and no RH claim",
        ],
        "provenance": {
            "script": os.fspath(Path(__file__).relative_to(ROOT)),
            "parent": "scripts/routea_weighted_zero_solve_enclosure_preflight_2201.py",
        },
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()

