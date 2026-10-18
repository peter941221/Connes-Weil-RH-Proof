#!/usr/bin/env python3
"""Export all Python recurrence stages for the concrete Route B bridge cell.

The output is input data for a future rational replay proof.  It is not a
Lean certificate: no claim is made that these endpoint boxes dominate the
Lean interval jet until each stage is checked there.
"""
from fractions import Fraction
import hashlib
import importlib.util
import json
import math
from pathlib import Path

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
PARENT = ROOT / "scripts/p3_certified_strip_constants_2720.py"
OUT = ROOT / "results/2840_route_b_cell4096_stage_bridge.json"


def exact_endpoint(interval, upper=True):
    sign, mantissa, exponent, _ = interval._mpi_[1 if upper else 0]
    value = Fraction((-1 if sign else 1) * mantissa)
    return value * (2 ** exponent if exponent >= 0 else Fraction(1, 2 ** -exponent))


def reciprocal_jet(X):
    out = [1 / X[0]]
    for n in range(len(X) - 1):
        total = sum((math.comb(n + 1, j + 1) * X[j + 1] * out[n - j]
                     for j in range(n + 1)), mp.iv.mpf(0))
        out.append(-total / X[0])
    return out


def stages(B, order):
    u = [B, mp.iv.mpf(1)] + [mp.iv.mpf(0)] * (order - 1)
    v = [1 - B, mp.iv.mpf(-1)] + [mp.iv.mpf(0)] * (order - 1)
    inv_u, inv_v = reciprocal_jet(u), reciprocal_jet(v)
    phase = [a - b for a, b in zip(inv_v, inv_u)]
    exp_jet = [mp.iv.exp(phase[0])]
    for n in range(order):
        exp_jet.append(sum((math.comb(n, j) * phase[j + 1] * exp_jet[n - j]
                            for j in range(n + 1)), mp.iv.mpf(0)))
    denominator = [exp_jet[0] + 1] + exp_jet[1:]
    inv_den = reciprocal_jet(denominator)
    transition = [sum((math.comb(k, j) * exp_jet[j] * inv_den[k - j]
                       for j in range(k + 1)), mp.iv.mpf(0))
                  for k in range(order + 1)]
    return {"phase": phase, "exp": exp_jet, "denominator": denominator,
            "reciprocal": inv_den, "transition": transition}


def box(x):
    return {"lo": str(exact_endpoint(x, False)), "hi": str(exact_endpoint(x, True))}


def main():
    spec = importlib.util.spec_from_file_location("p3_bounds2840", PARENT)
    p3 = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(p3)
    mp.iv.dps = 40
    lo = Fraction(1, 4096)
    width = (Fraction(1, 2) - lo) / 8192
    left, right = lo + 4096 * width, lo + 4097 * width
    B = mp.iv.mpf([mp.mpf(left.numerator) / left.denominator,
                   mp.mpf(right.numerator) / right.denominator])
    payload = {"record": 2840, "status": "STAGE_INPUT",
               "cell": 4096, "left": str(left), "right": str(right),
               "orders": {}, "parent_sha256": hashlib.sha256(PARENT.read_bytes()).hexdigest(),
               "nonclaims": ["Python model artifact only",
                             "no Lean interval domination",
                             "no ledger, SourceRH, or RH claim"]}
    for order in (4, 7):
        payload["orders"][str(order)] = {
            stage: [box(slot) for slot in slots]
            for stage, slots in stages(B, order).items()
        }
    OUT.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"record": 2840, "cell": 4096, "orders": [4, 7],
                      "stages": ["phase", "exp", "denominator", "reciprocal", "transition"]}))


if __name__ == "__main__":
    main()
