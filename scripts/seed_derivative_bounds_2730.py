#!/usr/bin/env python3
"""Directed interval integration plus analytic endpoint majorant.

Conditional on the documented derivative recurrences; not a Lean theorem.
No neighboring-cell endpoint proxy and no sampled endpoint validation.
"""
from fractions import Fraction
import hashlib
import importlib.util
import json
import math
from pathlib import Path
import sys

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
PARENT = ROOT / "scripts/p3_certified_strip_constants_2720.py"
OUT = ROOT / "results/2730_seed_derivative_bounds.json"


def exact_endpoint(interval, upper=True):
    sign, mantissa, exponent, _ = interval._mpi_[1 if upper else 0]
    value = Fraction((-1 if sign else 1) * mantissa)
    return value * (2 ** exponent if exponent >= 0 else Fraction(1, 2 ** -exponent))


def majorants(order):
    # |phi^(j)| <= 2*j!*x^(-2j), j>=1, 0<x<=1/2.
    b = [1]
    for k in range(order):
        b.append(sum(math.comb(k, j) * 2 * math.factorial(j + 1) * b[k-j]
                     for j in range(k + 1)))
    c = [1]
    for k in range(1, order + 1):
        c.append(sum(math.comb(k, j) * b[j] * c[k-j] for j in range(1, k + 1)))
    d = [sum(math.comb(k, j) * b[j] * c[k-j] for j in range(k + 1))
         for k in range(order + 1)]
    return b, c, d


def main():
    spec = importlib.util.spec_from_file_location("p3_bounds2730", PARENT)
    p3 = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(p3)
    mp.iv.dps = 40
    n = 8192
    order = 7
    b, c, d = majorants(order)
    a = Fraction(1, 4096)
    # 4*int_0^a |T^(k)| <= 32*d_k*a^(1-2k)*2^-4096.
    endpoint = {k: 32 * d[k] * a ** (1 - 2*k) / 2 ** 4096
                for k in range(1, order + 1)}
    assert all(a <= Fraction(1, 2*k) for k in endpoint)
    acc = {k: mp.iv.mpf(0) for k in endpoint}
    lo = mp.iv.mpf(1) / 4096
    width = (mp.iv.mpf(1) / 2 - lo) / n
    # All coordinates are dyadic and represented exactly at this precision.
    for i in range(n):
        left = lo + i * width
        right = lo + (i+1) * width
        cell = mp.iv.mpf([left.a, right.b])
        jet = p3.seed_jet(cell, order)
        for k in endpoint:
            mag = abs(jet[k])
            acc[k] += 4 * width * mp.iv.mpf([0, mag.b])
    bounds = {k: exact_endpoint(acc[k]) + endpoint[k] for k in endpoint}
    checks = {
        "first_order_encloses_exact_two": bounds[1] >= 2,
        "second_order_encloses_exact_eight": bounds[2] >= 8,
        "D4_le_1500": bounds[4] <= 1500,
        "D7_le_2e9": bounds[7] <= 2_000_000_000,
        "endpoint_negligible": all(v < Fraction(1, 10**1000) for v in endpoint.values()),
        "majorant_base": b[1] == 2 and c[1] == 2 and d[1] == 4,
    }
    rows = {str(k): {"upper_rational": str(bounds[k]),
                     "upper_decimal_diagnostic": float(bounds[k]),
                     "endpoint_upper_rational": str(endpoint[k])} for k in bounds}
    payload = {
        "record": 2730, "status": "INTERVAL-PASS" if all(checks.values()) else "CHECK-FAIL",
        "cells": n, "iv_dps": mp.iv.dps, "endpoint_a": str(a),
        "majorants": {"E": b, "reciprocal": c, "T": d},
        "bounds": rows, "checks": checks,
        "parent_sha256": hashlib.sha256(PARENT.read_bytes()).hexdigest(),
        "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "nonclaims": ["Derivative-jet identities and analytic majorants are paper derivations, not Lean facts.",
                      "No envelope constants, carrier transfer, gate, or universal-rho premise is certified here."]}
    OUT.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"checks": checks, "upper_bounds": {k: float(v) for k,v in bounds.items()}}, indent=2))
    return 0 if all(checks.values()) else 1


if __name__ == "__main__":
    sys.exit(main())
