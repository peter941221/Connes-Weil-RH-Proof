#!/usr/bin/env python3
"""Export the per-cell exact rational D4/D7 interval charges from record 2730.

This preserves the existing 2730 evaluator and makes its discarded cell
accumulators reviewable. It is a model artifact until the evaluator is linked
to the Lean jet semantics.
"""
from fractions import Fraction
import hashlib
import importlib.util
import json
from pathlib import Path

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
PARENT = ROOT / "scripts/p3_certified_strip_constants_2720.py"
OUT = ROOT / "results/2804_route_b_seed_d4_d7_cell_ledger.json"


def exact_endpoint(interval, upper=True):
    sign, mantissa, exponent, _ = interval._mpi_[1 if upper else 0]
    value = Fraction((-1 if sign else 1) * mantissa)
    return value * (2 ** exponent if exponent >= 0 else Fraction(1, 2 ** -exponent))


def main():
    spec = importlib.util.spec_from_file_location("p3_bounds2804", PARENT)
    p3 = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(p3)
    mp.iv.dps = 40
    n = 8192
    order = 7
    lo = mp.iv.mpf(1) / 4096
    width = (mp.iv.mpf(1) / 2 - lo) / n
    rows = []
    sums = {4: Fraction(0), 7: Fraction(0)}
    for i in range(n):
        left = lo + i * width
        right = lo + (i + 1) * width
        cell = mp.iv.mpf([left.a, right.b])
        jet = p3.seed_jet(cell, order)
        row = {"index": i, "left": str(exact_endpoint(left)),
               "right": str(exact_endpoint(right)), "charges": {}}
        for k in (4, 7):
            mag = abs(jet[k])
            charge = exact_endpoint(4 * width * mp.iv.mpf([0, mag.b]))
            sums[k] += charge
            row["charges"][str(k)] = str(charge)
        rows.append(row)
    payload = {
        "record": 2804, "source_record": 2730, "status": "LEDGER-GENERATED",
        "cells": n, "iv_dps": mp.iv.dps, "orders": [4, 7],
        "rows": rows,
        "sums": {str(k): str(v) for k, v in sums.items()},
        "parent_sha256": hashlib.sha256(PARENT.read_bytes()).hexdigest(),
        "nonclaims": [
            "This is a model artifact, not a Lean theorem.",
            "The p3 evaluator-to-Lean derivative soundness bridge remains open.",
            "No cardinal pin, SourceRH, or RH claim."
        ]
    }
    OUT.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"cells": n, "sums": {str(k): float(v) for k, v in sums.items()}}, indent=2))


if __name__ == "__main__":
    main()
