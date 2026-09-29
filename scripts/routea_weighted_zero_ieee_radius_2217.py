"""Record 2217: full-node AMP forward-error radius screen.

This is a parameterized IEEE-style forward-error calculation, not an interval
certificate.  It answers the concrete scope question left open by 2211:
does the exponent-argument and operation allowance stay controlled on every
node of the same 30-node finite candidate rule?
"""
import importlib.util
import json
import os
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sp = importlib.util.spec_from_file_location(
    "full2206", ROOT / "scripts" / "routea_weighted_zero_vector_split_full_refinement_2206.py")
parent = importlib.util.module_from_spec(sp)
sp.loader.exec_module(parent)

OUT = ROOT / "results" / "2217_weighted_zero_ieee_radius.json"
U = np.finfo(float).eps / 2.0
NSEG = 1100
NPAN = 12
AMP_FACTOR = 8.0
OP_FACTOR = 16.0


def one_node(node_index, node, fam, coeff, xw):
    gl_abs = 0.0
    sim_abs = 0.0
    exp_smear = 0.0
    term_count = 0
    for c, (a, theta), (X, W) in zip(coeff, fam, xw):
        z = a * (node + 1j * theta)
        f = np.exp(-parent.v.q.r.K / (1.0 - (X / a) ** 2) + z * X)
        gl_term = float(np.sum(np.abs(W * f)))
        gl_abs += abs(c) * gl_term
        term_count += len(X)
        lo_all, hi_all = -a * (1.0 - parent.DELTA), a * (1.0 - parent.DELTA)
        sim_local = 0.0
        for panel in range(NPAN):
            lo = lo_all + (hi_all - lo_all) * panel / NPAN
            hi = lo_all + (hi_all - lo_all) * (panel + 1) / NPAN
            xx = np.linspace(lo, hi, 2 * NSEG + 1)
            ff = np.exp(-parent.v.q.r.K / (1.0 - (xx / a) ** 2) + z * xx)
            hh = (hi - lo) / (2 * NSEG)
            weights = np.ones(len(xx))
            weights[1:-1:2] = 4.0
            weights[2:-1:2] = 2.0
            sim_local += float(hh / 3.0 * np.sum(weights * np.abs(ff)))
            term_count += len(xx)
        sim_abs += abs(c) * sim_local
        amp = AMP_FACTOR * U * abs(z) * a
        exp_smear += abs(c) * amp * (gl_term + sim_local)
    operation = OP_FACTOR * U * (gl_abs + sim_abs)
    return {
        "node_index": int(node_index),
        "node_real": float(np.real(node)),
        "node_imag": float(np.imag(node)),
        "gl_abs": gl_abs,
        "simpson_abs": sim_abs,
        "exp_argument_smear": exp_smear,
        "operation": operation,
        "total": exp_smear + operation,
        "term_count": term_count,
    }


def main():
    nodes, fam, A0, _b_base, b_corr = parent.v.r.matrices(parent.v.r.M_REF)
    coeff = np.linalg.solve(A0, b_corr)
    xw = [parent.v.q.r.r59.phi_weights(a, panels=6, m=parent.M)
          for a, _ in fam]
    rows = [one_node(index, node, fam, coeff, xw)
            for index, node in enumerate(nodes)]
    binding = max(rows, key=lambda row: row["total"])
    result = {
        "record": 2217,
        "status": "FULL-NODE-IEEE-FORWARD-RADIUS-SCREEN",
        "owner": {"nodes": len(nodes), "families": len(fam), "NSEG": NSEG,
                  "panels": NPAN, "rhs": "correction"},
        "model": {"unit_roundoff": U, "amp_factor": AMP_FACTOR,
                  "operation_factor": OP_FACTOR},
        "binding": binding,
        "min_total": min(row["total"] for row in rows),
        "max_total": binding["total"],
        "rows": rows,
        "reference": {
            "2211_binding_total": 2.4594248e-8,
            "2211_combined_correction": 6.2550323e-5,
            "screen": "full-node maximum is compared to the 2211 binding row;"
                      " this remains a forward-error price, not an outward proof",
        },
        "nonclaims": [
            "stored NumPy values are not outward intervals",
            "IEEE operation model is parameterized by the standard U factors",
            "no complete-owner transfer and no RH claim",
        ],
        "provenance": {
            "script": os.fspath(Path(__file__).relative_to(ROOT)),
            "parent": "scripts/routea_weighted_zero_transcendental_allowance_2211.py",
        },
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: result[k] for k in
                      ("record", "status", "binding", "min_total", "max_total")},
                     indent=2))


if __name__ == "__main__":
    main()
