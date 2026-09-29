"""Record 2205: binding-node refinement of the vector-aware split price."""
import importlib.util
import json
import os
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
sp = importlib.util.spec_from_file_location(
    "v2204", ROOT / "scripts" / "routea_weighted_zero_vector_split_price_2204.py")
v = importlib.util.module_from_spec(sp)
sp.loader.exec_module(v)
v.NSEG = 1000

OUT = ROOT / "results" / "2205_weighted_zero_vector_split_binding_refinement.json"


def main():
    nodes, fam, A0, b_base, b_corr = v.r.matrices(v.r.M_REF)
    XW = [v.q.r.r59.phi_weights(a, panels=6, m=v.M) for a, _ in fam]
    rows = []
    for rhs, b, node in (("base", b_base, 29), ("correction", b_corr, 2)):
        coeff = __import__("numpy").linalg.solve(A0, b)
        s = nodes[node]
        gl_minus_s = 0.0j
        gl_edge = 0.0j
        err_s = 0.0
        edge_i = 0.0
        for c, (a, theta), xw in zip(coeff, fam, XW):
            gi, si, ge, es, ei = v.family_terms(a, a * (s + 1j * theta), xw)
            gl_minus_s += c * (gi - si)
            gl_edge += c * ge
            err_s += abs(c) * es
            edge_i += abs(c) * ei
        bound = abs(gl_minus_s) + err_s + abs(gl_edge) + edge_i
        rows.append({
            "rhs": rhs, "node": node, "bound": float(bound),
            "computed_inner_difference": float(abs(gl_minus_s)),
            "simpson_remainder": float(err_s),
            "computed_edge_sum": float(abs(gl_edge)),
            "edge_integral_bound": float(edge_i),
            "coefficient_inf": float(max(abs(coeff))),
        })
    result = {
        "record": 2205,
        "status": "VECTOR-SPLIT-BINDING-REFINEMENT",
        "NSEG": v.NSEG, "rows": rows,
        "nonclaims": [
            "only binding nodes were recomputed",
            "floating sums are not outward intervals",
            "no complete-owner transfer and no RH claim",
        ],
        "provenance": {
            "script": os.fspath(Path(__file__).relative_to(ROOT)),
            "parent": "scripts/routea_weighted_zero_vector_split_price_2204.py",
        },
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()

