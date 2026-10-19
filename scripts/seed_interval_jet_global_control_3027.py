#!/usr/bin/env python3
"""Global canonical-vs-legacy interval convention control for all 8192 cells.

This is an independent numerical control.  It does not promote mpmath
intervals to a Lean theorem; it checks that the Python ledger evaluator uses
the same jet recurrence and endpoint convention as the canonical replay.
"""
import hashlib
import importlib.util
import json
import math
from fractions import Fraction
from pathlib import Path

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
PARENT = ROOT / "scripts/p3_certified_strip_constants_2720.py"
OUT = ROOT / "results/3027_seed_interval_jet_global_control.json"


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
    return [sum((math.comb(k, j) * E[j] * R[k-j]
                 for j in range(k + 1)), mp.iv.mpf(0))
            for k in range(order + 1)]


def endpoint(x):
    sign, mantissa, exponent, _ = x._mpi_[1]
    value = Fraction((-1 if sign else 1) * mantissa)
    return value * (2 ** exponent if exponent >= 0 else Fraction(1, 2 ** -exponent))


def main():
    spec = importlib.util.spec_from_file_location("p3_control3027", PARENT)
    p3 = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(p3)
    mp.iv.dps = 40
    n = 8192
    order = 7
    lo = mp.iv.mpf(1) / 4096
    width = (mp.iv.mpf(1) / 2 - lo) / n
    max_dev = [mp.mpf(0) for _ in range(order + 1)]
    containment = [True for _ in range(order + 1)]
    for i in range(n):
        left = lo + i * width
        right = lo + (i + 1) * width
        cell = mp.iv.mpf([left.a, right.b])
        canonical = canonical_transition_jet(cell, order)
        legacy = p3.seed_jet(cell, order)
        for k in range(order + 1):
            cl, cu = mp.mpf(canonical[k].a), mp.mpf(canonical[k].b)
            ll, lu = mp.mpf(legacy[k].a), mp.mpf(legacy[k].b)
            scale = max(abs(cl), abs(cu), abs(ll), abs(lu), 1)
            max_dev[k] = max(max_dev[k], max(abs(cl - ll), abs(cu - lu)) / scale)
            containment[k] = containment[k] and cl <= ll and lu <= cu
    checks = {
        "cells": n,
        "all_contained": all(containment),
        "max_deviation_below_1e-25": all(v <= mp.mpf("1e-25") for v in max_dev),
    }
    payload = {
        "record": 3027,
        "status": "CONTROL-PASS" if all(checks.values()) else "CONTROL-FAIL",
        "cells": n,
        "max_normalized_deviation": [mp.nstr(v, 20) for v in max_dev],
        "containment_by_order": containment,
        "checks": checks,
        "parent_sha256": hashlib.sha256(PARENT.read_bytes()).hexdigest(),
        "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "nonclaims": [
            "Numerical mpmath interval control only.",
            "Does not prove evaluator-to-Lean soundness or D4/D7/RH."
        ],
    }
    OUT.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(payload, indent=2))
    return 0 if all(checks.values()) else 1


if __name__ == "__main__":
    raise SystemExit(main())
