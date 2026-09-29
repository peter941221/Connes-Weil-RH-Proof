"""Record 2220: certified implementation-radius replacement for 2219.

The exact-Fraction bracket certifies the mathematical complex exponential and
charges its distance from the returned binary64 value as an implementation
remainder.  This does not assume correct rounding.
"""
import importlib.util
import json
import math
import os
import sys
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
spec = importlib.util.spec_from_file_location(
    "atom2219", ROOT / "scripts" / "routea_weighted_zero_binary64_exp_atom_2219.py")
atom = importlib.util.module_from_spec(spec)
spec.loader.exec_module(atom)

OUT = ROOT / "results" / "2220_exp_implementation_radius.json"


def radius_meta(q: F):
    return {"sign": (q > 0) - (q < 0),
            "numerator_bits": abs(q.numerator).bit_length(),
            "denominator_bits": q.denominator.bit_length()}


def one_radius(iv, value: float):
    center = F.from_float(value)
    radius = max(center - iv.lo, iv.hi - center)
    lo, hi = atom.float_cell(value)
    ulp_cell = hi - lo
    return {
        "radius": radius_meta(radius),
        "ulp_cell": radius_meta(ulp_cell),
        "radius_float": float(radius),
        "value_abs": abs(value),
        "radius_over_value_abs": float(radius) / max(abs(value), math.ldexp(1.0, -1074)),
        "radius_over_ulp_cell": float(radius / ulp_cell),
        "finite": math.isfinite(value),
    }


def main():
    nodes, fam, _A0, _bb, _bc = atom.parent.v.r.matrices(atom.parent.v.r.M_REF)
    node = atom.NODE
    family_indices = sorted({0, len(fam) // 2, len(fam) - 1})
    samples = []
    for family_index in family_indices:
        a, theta = fam[family_index]
        X, _W = atom.parent.v.q.r.r59.phi_weights(
            a, panels=6, m=atom.parent.M)
        point_index = len(X) // 2
        xf = float(X[point_index])
        z = a * (nodes[node] + 1j * theta)
        q = -atom.parent.v.q.r.K / (1.0 - (xf / a) ** 2) + z * xf
        qr, qi = F.from_float(float(np.real(q))), F.from_float(float(np.imag(q)))
        re_iv, im_iv = atom.complex_exp_bracket(qr, qi)
        out = np.exp(q)
        samples.append({
            "family": family_index,
            "point": point_index,
            "q_real": str(qr),
            "q_imag": str(qi),
            "real": one_radius(re_iv, float(np.real(out))),
            "imag": one_radius(im_iv, float(np.imag(out))),
        })
    result = {
        "record": 2220,
        "status": "EXP-IMPLEMENTATION-RADIUS-CERTIFICATE",
        "scope": {"node_index": node, "families_selected": family_indices,
                  "samples_per_family": 1, "samples": len(samples)},
        "method": "exact Fraction exp/sin/cos brackets; radius around returned binary64 value",
        "samples": samples,
        "nonclaims": [
            "atomic samples do not certify every quadrature term",
            "input exponent construction and summation are not certified",
            "no complete-owner transfer and no RH claim",
        ],
        "provenance": {
            "script": os.fspath(Path(__file__).relative_to(ROOT)),
            "replaces": "2219 rounding-cell-only assumption",
        },
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"record": 2220, "status": result["status"],
                      "samples": len(samples),
                      "max_radius_over_ulp_cell": max(
                          max(s["real"]["radius_over_ulp_cell"],
                              s["imag"]["radius_over_ulp_cell"])
                          for s in samples)}, indent=2))


if __name__ == "__main__":
    import numpy as np
    main()
