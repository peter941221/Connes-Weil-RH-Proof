"""Record 2219: exact-rational binary64 exp atom certificate.

For selected exponent arguments on the binding row, this script evaluates
sin/cos/exp brackets with exact Fraction arithmetic and checks that the whole
mathematical complex exponential bracket lies inside the binary64 rounding
cell of NumPy's returned complex value.  It is an atomic evaluator certificate
and deliberately does not claim the full owner or the complete operation
chain.
"""
import importlib.util
import json
import math
import os
import sys
from fractions import Fraction as F
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts" / "yoshida_intervals"))
from yoshida_interval_gen import (  # noqa: E402
    Interval,
    add,
    const_interval,
    elementary_bracket,
    mul,
)

sp = importlib.util.spec_from_file_location(
    "full2206", ROOT / "scripts" / "routea_weighted_zero_vector_split_full_refinement_2206.py")
parent = importlib.util.module_from_spec(sp)
sp.loader.exec_module(parent)

OUT = ROOT / "results" / "2219_binary64_exp_atom.json"
NODE = 2
WIDTH = F(1, 10**18)


def exp_pos_bounds(a: F, terms: int = 96) -> tuple[F, F]:
    """Exact exp(a) bracket using range reduction and a geometric tail."""
    if a < 0:
        raise ValueError("positive argument required")
    scale = 1
    while F(scale) < a:
        scale *= 2
    r = a / F(scale)
    term = F(1)
    lower = F(1)
    for n in range(1, terms):
        term *= r / F(n)
        lower += term
    next_term = term * r / F(terms)
    ratio = r / F(terms + 1)
    upper = lower + next_term / (F(1) - ratio)
    for _ in range(scale.bit_length() - 1):
        lower *= lower
        upper *= upper
    return lower, upper


def exp_lower_pos(a: F) -> F:
    return exp_pos_bounds(a)[0]


def exp_upper_pos(a: F) -> F:
    return exp_pos_bounds(a)[1]


def _old_exp_upper_pos(a: F, slack: F = F(1, 10**22)) -> F:
    """Retained only as a diagnostic reference for the old slow path."""
    total = F(0)
    term = F(1)
    n = 0
    while True:
        total += term
        n += 1
        term *= a / F(n)
        if n + 1 > a:
            tail = term * F(n + 1) / F(n + 1 - a)
            if tail <= slack:
                return total + tail


def real_exp_bracket(x: Interval) -> Interval:
    """Exact Taylor bracket for exp on a rational interval."""
    if x.lo >= 0:
        return Interval(exp_lower_pos(x.lo), exp_upper_pos(x.hi))
    if x.hi <= 0:
        return Interval(
            F(1) / exp_upper_pos(-x.lo),
            F(1) / exp_lower_pos(-x.hi),
        )
    return Interval(F(1) / exp_upper_pos(-x.lo), exp_upper_pos(x.hi))


def complex_exp_bracket(qr: F, qi: F):
    x = real_exp_bracket(const_interval(qr))
    y = const_interval(qi)
    co, _ = elementary_bracket("cos", y, width_target=WIDTH, terms_cap=4096)
    si, _ = elementary_bracket("sin", y, width_target=WIDTH, terms_cap=4096)
    return mul(x, co), mul(x, si)


def float_cell(v: float):
    if not math.isfinite(v):
        raise ValueError("non-finite output")
    lo = math.nextafter(v, -math.inf)
    hi = math.nextafter(v, math.inf)
    fv = F.from_float(v)
    return (F.from_float(lo) + fv) / 2, (fv + F.from_float(hi)) / 2


def fraction_meta(q: F):
    return {"sign": (q > 0) - (q < 0),
            "numerator_bits": abs(q.numerator).bit_length(),
            "denominator_bits": q.denominator.bit_length()}


def check_component(iv: Interval, v: float):
    lo, hi = float_cell(v)
    return {
        "contained": lo <= iv.lo and iv.hi <= hi,
        "interval_width": fraction_meta(iv.width()),
        "cell_width": fraction_meta(hi - lo),
        "lower_gap": fraction_meta(iv.lo - lo),
        "upper_gap": fraction_meta(hi - iv.hi),
    }


def main():
    nodes, fam, _A0, _bb, _bc = parent.v.r.matrices(parent.v.r.M_REF)
    samples = []
    # A deliberately small atomic smoke: one central GL point on three
    # geometrically distinct families.  Full-term coverage remains open.
    family_indices = sorted({0, len(fam) // 2, len(fam) - 1})
    for family_index in family_indices:
        a, theta = fam[family_index]
        X, _W = parent.v.q.r.r59.phi_weights(a, panels=6, m=parent.M)
        for point_index in (len(X) // 2,):
            xf = float(X[point_index])
            z = a * (nodes[NODE] + 1j * theta)
            q = -parent.v.q.r.K / (1.0 - (xf / a) ** 2) + z * xf
            qr, qi = F.from_float(float(np.real(q))), F.from_float(float(np.imag(q)))
            re_iv, im_iv = complex_exp_bracket(qr, qi)
            out = np.exp(q)
            re_check = check_component(re_iv, float(np.real(out)))
            im_check = check_component(im_iv, float(np.imag(out)))
            samples.append({
                "family": family_index,
                "point": point_index,
                "q_real": str(qr),
                "q_imag": str(qi),
                "numpy_real": float(np.real(out)),
                "numpy_imag": float(np.imag(out)),
                "real": re_check,
                "imag": im_check,
            })
    failures = [s for s in samples
                if not s["real"]["contained"] or not s["imag"]["contained"]]
    result = {
        "record": 2219,
        "status": "BINARY64-EXP-ATOM-CERTIFICATE",
        "scope": {"node_index": NODE, "families_selected": family_indices,
                  "samples_per_family": 1, "samples": len(samples)},
        "interval": {"arithmetic": "exact Fraction", "target_width": str(WIDTH),
                      "rounding_cell": "midpoints of exact adjacent binary64 values"},
        "passed": not failures,
        "failure_count": len(failures),
        "samples": samples,
        "nonclaims": [
            "atomic samples do not certify every quadrature term",
            "input exponent construction and summation are not certified",
            "no complete-owner transfer and no RH claim",
        ],
        "provenance": {
            "script": os.fspath(Path(__file__).relative_to(ROOT)),
            "parent": "scripts/routea_weighted_zero_ieee_radius_2217.py",
        },
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: result[k] for k in
                      ("record", "status", "scope", "passed", "failure_count")},
                     indent=2))
    if failures:
        raise SystemExit("binary64 exp atom containment failed")


if __name__ == "__main__":
    main()
