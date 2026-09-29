"""Record 2221: full-owner price of a black-box exp bound.

This uses only |exp(q)-v| <= exp(Re q)+|v|, so it makes no library
correctness assumption.  It is a deliberately coarse quantitative no-go for
replacing an implementation certificate by a black-box triangle inequality.
"""
import importlib.util
import json
import math
import os
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sp = importlib.util.spec_from_file_location(
    "full2206", ROOT / "scripts" / "routea_weighted_zero_vector_split_full_refinement_2206.py")
parent = importlib.util.module_from_spec(sp)
sp.loader.exec_module(parent)

OUT = ROOT / "results" / "2221_exp_blackbox_no_go.json"
NSEG = 1100
NPAN = 12
TARGET = 6.2550323e-5


def one_node(node_index, node, fam, coeff, xw):
    gl = 0.0
    sim = 0.0
    terms = 0
    for c, (a, theta), (X, W) in zip(coeff, fam, xw):
        z = a * (node + 1j * theta)
        q = -parent.v.q.r.K / (1.0 - (X / a) ** 2) + z * X
        f = np.exp(q)
        # |exp(q)-v| <= |exp(q)| + |v| = exp(Re q) + |v|.
        gl += abs(c) * float(np.sum(np.abs(W) * (np.exp(np.real(q)) + np.abs(f))))
        lo_all, hi_all = -a * (1.0 - parent.DELTA), a * (1.0 - parent.DELTA)
        local = 0.0
        for panel in range(NPAN):
            lo = lo_all + (hi_all - lo_all) * panel / NPAN
            hi = lo_all + (hi_all - lo_all) * (panel + 1) / NPAN
            xx = np.linspace(lo, hi, 2 * NSEG + 1)
            qq = -parent.v.q.r.K / (1.0 - (xx / a) ** 2) + z * xx
            ff = np.exp(qq)
            hh = (hi - lo) / (2 * NSEG)
            weights = np.ones(len(xx))
            weights[1:-1:2] = 4.0
            weights[2:-1:2] = 2.0
            local += float(hh / 3.0 * np.sum(weights *
                                               (np.exp(np.real(qq)) + np.abs(ff))))
            terms += len(xx)
        sim += abs(c) * local
    return {"node_index": int(node_index), "node_real": float(np.real(node)),
            "node_imag": float(np.imag(node)), "gl_blackbox": gl,
            "simpson_blackbox": sim, "total": gl + sim, "term_count": terms}


def main():
    nodes, fam, A0, _b, b_corr = parent.v.r.matrices(parent.v.r.M_REF)
    coeff = np.linalg.solve(A0, b_corr)
    xw = [parent.v.q.r.r59.phi_weights(a, panels=6, m=parent.M)
          for a, _ in fam]
    rows = [one_node(i, node, fam, coeff, xw) for i, node in enumerate(nodes)]
    binding = max(rows, key=lambda row: row["total"])
    result = {
        "record": 2221,
        "status": "BLACKBOX-EXP-TRIANGLE-SCOPED-NO-GO",
        "owner": {"nodes": len(nodes), "families": len(fam),
                  "NSEG": NSEG, "panels": NPAN},
        "bound": "|exp(q)-v| <= exp(Re q)+|v|",
        "target_combined_correction": TARGET,
        "binding": binding,
        "max_blackbox": binding["total"],
        "ratio_to_target": binding["total"] / TARGET,
        "rows": rows,
        "nonclaims": ["not an RH claim", "does not reject a certified implementation remainder"],
        "provenance": {"script": os.fspath(Path(__file__).relative_to(ROOT)),
                       "source_budget": "2211 combined correction"},
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: result[k] for k in
                      ("record", "status", "max_blackbox", "ratio_to_target")}, indent=2))


if __name__ == "__main__":
    main()
