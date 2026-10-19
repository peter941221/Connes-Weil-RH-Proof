#!/usr/bin/env python3
"""Export the 2730 interval upper for every cell as rational data."""
import importlib.util, json
from fractions import Fraction
from pathlib import Path
import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
PARENT = ROOT / "scripts/p3_certified_strip_constants_2720.py"
OUT = ROOT / "results/3040_seed_d4d7_cell_upper.json"

def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m

def endpoint_majorant(order):
    # Same analytic majorant constants and endpoint interval as record 2730.
    import math
    b = [1]
    for k in range(order):
        b.append(sum(math.comb(k, j) * 2 * math.factorial(j + 1) * b[k-j]
                     for j in range(k + 1)))
    c = [1]
    for k in range(1, order + 1):
        c.append(sum(math.comb(k, j) * b[j] * c[k-j] for j in range(1, k + 1)))
    d = [sum(math.comb(k, j) * b[j] * c[k-j] for j in range(k + 1))
         for k in range(order + 1)]
    a = Fraction(1, 4096)
    return Fraction(32 * d[order]) * a ** (1 - 2 * order) / 2 ** 4096

def main():
    p3 = load(PARENT, "p3_3040")
    mp.iv.dps = 40; n = 8192
    lo = mp.iv.mpf(1) / 4096
    width = (mp.iv.mpf(1) / 2 - lo) / n
    endpoint = {k: endpoint_majorant(k) for k in (4, 7)}
    rows = []
    sums = {4: Fraction(0), 7: Fraction(0)}
    for i in range(n):
        left = lo + i * width; right = lo + (i + 1) * width
        jet = p3.seed_jet(mp.iv.mpf([left.a, right.b]), 7)
        row = {"index": i}
        for k in (4, 7):
            upper = mp.mpf((4 * width * mp.iv.mpf([0, abs(jet[k]).b])).b)
            q = Fraction(str(mp.nstr(upper, 50))) + endpoint[k] / n
            row[str(k)] = str(q); sums[k] += q
        rows.append(row)
    payload = {"record": 3040, "status": "CELL-UPPER-EXPORTED", "cells": n,
               "endpoint_majorant": {str(k): str(v) for k, v in endpoint.items()},
               "sums": {str(k): str(v) for k, v in sums.items()}, "rows": rows,
               "nonclaims": ["mpmath interval upper data only", "Lean evaluator soundness remains open"]}
    OUT.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"record": 3040, "cells": n, "sums": {str(k): float(v) for k,v in sums.items()},
                      "D4_lt_1500": sums[4] < 1500, "D7_lt_2e9": sums[7] < 2_000_000_000}, indent=2))

if __name__ == "__main__": main()
