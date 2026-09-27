#!/usr/bin/env python3
"""Record 2030: determinant certification margin on the converged gate rows.

Pure post-processing of results/2028_coupling_scan.json.  For every measured
gate row it solves, exactly (Fraction arithmetic, no floating point), the
relative-precision budget of the map-106 section 4 certificate

    Clo      = C0 - eC                   > 0
    blo      = a*C0 + U0 - |a|*eC - eU   > 0
    detUpper = C0*V0 - U0^2 + E          < 0
    E        = |V0|*eC + |C0|*eV + eC*eV + 2*|U0|*eU + eU^2

in two centering frames, with a single number eps and
eC = eps*|C0|, eU = eps*|U0|, eV = eps*|V0|:

  frame  0    a = 0                    (uncentered; U0 = b0, V0 = D0)
  frame  V    a = rational near b0/C0  (vertex-centered; U0 ~ 0)

Outputs the eps that makes detUpper = 0 exactly, the eps that makes
Clo = 0, the eps that makes blo = 0, and whether the sign half of the
certificate is reachable at all from these centers.
"""

from __future__ import annotations

import json
import math
import sys
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RESULTS = ROOT / "results"

# relative rational quantization of the vertex center: a = round(a*2^20)/2^20
CENTER_BITS = 20


def to_fraction(x: float) -> F:
    return F(x).limit_denominator(10 ** 15)


SQRT_SCALE = 10 ** 15


def rat_sqrt(x: F) -> F:
    """Rational square root to ~1e-15 relative, without floating point."""
    p, q = x.numerator, x.denominator
    s = SQRT_SCALE
    return F(math.isqrt(p * q) if False else math.isqrt(p * q * s * s),
             q * s)


def solve_eps(Q: F, target: F) -> F:
    """Largest eps with (eps^2 + 2*eps) * Q = target, i.e. E = |det|."""
    return -1 + rat_sqrt(1 + target / Q)


def frame(a: F, C0: F, b0: F, D0: F) -> dict:
    U0 = b0 - a * C0
    V0 = D0 - 2 * a * b0 + a * a * C0
    det = C0 * V0 - U0 * U0
    CV = abs(C0 * V0)
    UU = U0 * U0
    Q = CV + UU
    # detUpper(eps) = det + (eps^2 + 2*eps)*Q
    eps_det = solve_eps(Q, -det) if det < 0 else None
    # Clo(eps) = C0 - eps*|C0| > 0 ; blo(eps) = b0 - eps*(|a|*|C0| + |U0|) > 0
    eps_C = F(abs(C0)) / abs(C0) if C0 > 0 else None
    slope_b = abs(a) * abs(C0) + abs(U0)
    eps_b = (b0 / slope_b) if (b0 > 0 and slope_b > 0) else None
    return {
        "a": float(a), "U0": float(U0), "V0": float(V0), "det": float(det),
        "eps_det_upper_zero": (float(eps_det) if eps_det is not None else None),
        "eps_Clo_zero": (float(eps_C) if eps_C is not None else None),
        "eps_blo_zero": (float(eps_b) if eps_b is not None else None),
        "C0_positive": bool(C0 > 0), "b0_positive": bool(b0 > 0),
        "det_negative": bool(det < 0),
        "det_over_Q": float(-det / Q) if det < 0 else None,
    }


def main() -> None:
    scan = json.loads((RESULTS / "2028_coupling_scan.json").read_text())
    rows = []
    for row in scan["trend"]:
        if "C" not in row:
            continue
        C0 = to_fraction(row["C"])
        b0 = to_fraction(row["b"])
        D0 = to_fraction(row["D"])
        q = F(2 ** CENTER_BITS)
        a_vertex = F(round(float(b0 / C0) * 2 ** CENTER_BITS), 2 ** CENTER_BITS)
        rows.append({
            "n": row["n"],
            "route_key": row["route_key"],
            "certified": row["route_key"] in scan["certified_routes"],
            "C": float(C0), "b": float(b0), "D": float(D0),
            "lambda_vertex": float(b0 / C0),
            "center_quantization": "1/2^%d" % CENTER_BITS,
            "frame_0": frame(F(0), C0, b0, D0),
            "frame_vertex": frame(a_vertex, C0, b0, D0),
        })

    report = {
        "record": 2030,
        "status": "DETERMINANT-WELL-CONDITIONED / SIGN-HALF-IS-THE-OBLIGATION",
        "source_artifact": "results/2028_coupling_scan.json",
        "source_grid": "dxi = 0.02 (<= 7.3e-7 relative on the finest grid)",
        "certificate": "docs/map/106 section 4",
        "rows": rows,
        "route_a_reference": {
            "note": "record 2010/2013 conditioning number f = mm/A at the "
                    "committed Route-A anchors; 1/f is the relative precision "
                    "the Route-A margin needs",
            "f": {"G5-H": 7196, "G5-W": 86087, "G7-H": 133, "G8-H": 51},
            "one_over_f": {k: 1.0 / v for k, v in
                           {"G5-H": 7196, "G5-W": 86087,
                            "G7-H": 133, "G8-H": 51}.items()},
        },
    }
    out = RESULTS / "2030_determinant_margin.json"
    out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8",
                    newline="\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
