"""Record 2222: exact exp implementation radii for all selected families.

This extends 2220 from three representative families to every family at the
central GL atom on the binding node. It remains an atom-level certificate.
"""
import importlib.util
import json
import os
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sp = importlib.util.spec_from_file_location(
    "radius2220", ROOT / "scripts" / "routea_weighted_zero_exp_implementation_radius_2220.py")
radius = importlib.util.module_from_spec(sp)
sp.loader.exec_module(radius)
atom = radius.atom
OUT = ROOT / "results" / "2222_exp_all_family_atoms.json"


def main():
    nodes, fam, _A0, _bb, _bc = atom.parent.v.r.matrices(atom.parent.v.r.M_REF)
    node = atom.NODE
    samples = []
    for family_index, (a, theta) in enumerate(fam):
        X, _W = atom.parent.v.q.r.r59.phi_weights(a, panels=6, m=atom.parent.M)
        point_index = len(X) // 2
        xf = float(X[point_index])
        z = a * (nodes[node] + 1j * theta)
        q = -atom.parent.v.q.r.K / (1.0 - (xf / a) ** 2) + z * xf
        qr, qi = atom.F.from_float(float(np.real(q))), atom.F.from_float(float(np.imag(q)))
        re_iv, im_iv = atom.complex_exp_bracket(qr, qi)
        out = np.exp(q)
        samples.append({
            "family": family_index,
            "point": point_index,
            "real": radius.one_radius(re_iv, float(np.real(out))),
            "imag": radius.one_radius(im_iv, float(np.imag(out))),
        })
    result = {
        "record": 2222,
        "status": "ALL-FAMILY-EXP-IMPLEMENTATION-RADIUS-CERTIFICATE",
        "scope": {"node_index": node, "families": len(fam),
                  "points_per_family": 1, "samples": len(samples)},
        "method": "exact Fraction exp/sin/cos brackets; radius around returned binary64 value",
        "max_radius_over_ulp_cell": max(
            max(s["real"]["radius_over_ulp_cell"], s["imag"]["radius_over_ulp_cell"])
            for s in samples),
        "max_radius_over_value_abs": max(
            max(s["real"]["radius_over_value_abs"], s["imag"]["radius_over_value_abs"])
            for s in samples),
        "samples": samples,
        "nonclaims": [
            "central GL atom only; complete quadrature terms remain open",
            "input exponent construction and finite summation are not certified",
            "no complete-owner transfer and no RH claim",
        ],
        "provenance": {"script": os.fspath(Path(__file__).relative_to(ROOT)),
                       "extends": "2220 three-family atom certificate"},
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: result[k] for k in
                      ("record", "status", "scope", "max_radius_over_ulp_cell",
                       "max_radius_over_value_abs")}, indent=2))


if __name__ == "__main__":
    main()
