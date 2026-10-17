#!/usr/bin/env python3
"""One-cell convention control; not a rational interval replay certificate."""
from fractions import Fraction
import hashlib
import importlib.util
import json
import math
from pathlib import Path
import sys
import time

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
PARENT = ROOT / "scripts/p3_certified_strip_constants_2720.py"


def reciprocal_jet(X):
    if mp.mpf(X[0].a) <= 0:
        raise ValueError("positive reciprocal interval required")
    inverse0 = 1 / X[0]
    out = [inverse0]
    for n in range(len(X) - 1):
        total = sum((math.comb(n + 1, j + 1) * X[j + 1] * out[n - j]
                     for j in range(n + 1)), mp.iv.mpf(0))
        out.append((-total) * inverse0)
    return out


def exponential_jet(X):
    out = [mp.iv.exp(X[0])]
    for n in range(len(X) - 1):
        out.append(sum((math.comb(n, j) * X[j + 1] * out[n - j]
                        for j in range(n + 1)), mp.iv.mpf(0)))
    return out


def canonical_transition_jet(B, order):
    u = [B, mp.iv.mpf(1)] + [mp.iv.mpf(0)] * (order - 1)
    v = [1 - B, mp.iv.mpf(-1)] + [mp.iv.mpf(0)] * (order - 1)
    inv_u, inv_v = reciprocal_jet(u), reciprocal_jet(v)
    phase = [b - a for a, b in zip(inv_u, inv_v)]
    E = exponential_jet(phase)
    denominator = [E[0] + 1] + E[1:]
    R = reciprocal_jet(denominator)
    return [sum((math.comb(k, j) * E[j] * R[k-j] for j in range(k+1)), mp.iv.mpf(0))
            for k in range(order+1)]


def main():
    started = time.monotonic()
    spec = importlib.util.spec_from_file_location("p3_control2734", PARENT)
    p3 = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(p3)
    mp.iv.dps = 40
    mp.mp.dps = 80
    a = Fraction(1, 4096)
    width = (Fraction(1, 2) - a) / 8192
    left = a + 4096 * width
    right = left + width
    lo = mp.mpf(left.numerator) / left.denominator
    hi = mp.mpf(right.numerator) / right.denominator
    B = mp.iv.mpf([lo, hi])
    canonical = canonical_transition_jet(B, 7)
    legacy = p3.seed_jet(B, 7)
    T = lambda x: mp.exp(-1/x + 1/(1-x)) / (1 + mp.exp(-1/x + 1/(1-x)))
    checks = {"cell_in_open_unit_interval": 0 < left < right < 1,
              "cell_is_exact_original_grid": right - left == width}
    rows = {}
    worst = mp.mpf(0)
    for k in range(8):
        cl, cu = mp.mpf(canonical[k].a), mp.mpf(canonical[k].b)
        ll, lu = mp.mpf(legacy[k].a), mp.mpf(legacy[k].b)
        scale = max(abs(cl), abs(cu), abs(ll), abs(lu), 1)
        dev = max(abs(cl-ll), abs(cu-lu)) / scale
        worst = max(worst, dev)
        checks["endpoint_convention_" + str(k)] = dev <= mp.mpf("1e-25")
        values = []
        for index, x in enumerate([lo, (lo + hi)/2, hi]):
            truth = mp.diff(T, x, k)
            checks["truth_containment_%d_%d" % (k, index)] = bool(cl <= truth <= cu and ll <= truth <= lu)
            values.append(mp.nstr(truth, 30))
        rows[str(k)] = {"canonical": [mp.nstr(cl, 45), mp.nstr(cu, 45)],
                        "legacy": [mp.nstr(ll, 45), mp.nstr(lu, 45)],
                        "normalized_endpoint_difference": mp.nstr(dev, 15), "point_values": values}
    out = {"record": 2734, "status": "CONTROL-PASS" if all(checks.values()) else "CONTROL-FAIL",
           "cell": {"left": str(left), "right": str(right), "index": 4096, "grid_cells": 8192},
           "checks": checks, "slots": rows, "worst_normalized_endpoint_difference": mp.nstr(worst, 15),
           "parent_sha256": hashlib.sha256(PARENT.read_bytes()).hexdigest(),
           "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
           "elapsed_seconds": time.monotonic() - started,
           "nonclaims": ["Only one cell and three points per slot; no global numerical certificate.",
                         "Floating interval convention control is not rational replay in Lean."]}
    (ROOT / "results/2734_seed_interval_jet_control.json").write_text(json.dumps(out, indent=2) + "\n")
    print(out["status"], "checks", len(checks), "worst", mp.nstr(worst, 15))
    return 0 if all(checks.values()) else 1


if __name__ == "__main__":
    sys.exit(main())
