#!/usr/bin/env python3
"""Full 8192-cell model reprice under the Lean-certified sharp e0 box."""
import importlib.util
import json
from pathlib import Path
import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
PARENT = ROOT / "scripts/p3_certified_strip_constants_2720.py"
OUT = ROOT / "results/2865_route_b_sharp_e0_full_reprice.json"

spec = importlib.util.spec_from_file_location("p3_2865", PARENT)
p3 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(p3)

def seed_jet_sharp(B, order):
    n = order + 1
    U = [mp.iv.mpf(0)] * n
    U[0], U[1] = B, mp.iv.mpf(1)
    V = [mp.iv.mpf(0)] * n
    V[0], V[1] = 1 - B, mp.iv.mpf(-1)
    iu, iv = p3.jet_recip(U), p3.jet_recip(V)
    phase = [a - b for a, b in zip(iv, iu)]
    E = p3.jet_exp(phase)
    E[0] = mp.iv.mpf([mp.mpf(1)/16, mp.mpf(1)/8])
    one = [mp.iv.mpf(0)] * n
    one[0] = mp.iv.mpf(1)
    R = p3.jet_recip([e + o for e, o in zip(E, one)])
    return p3.jet_mul(E, R)

def main():
    mp.iv.dps = 40
    cells, order = 8192, 7
    lo = mp.iv.mpf(1) / 4096
    width = (mp.iv.mpf(1) / 2 - lo) / cells
    sums = {4: mp.iv.mpf(0), 7: mp.iv.mpf(0)}
    maxima = {4: mp.iv.mpf(0), 7: mp.iv.mpf(0)}
    for i in range(cells):
        a, b = lo + i * width, lo + (i + 1) * width
        J = seed_jet_sharp(mp.iv.mpf([a.a, b.b]), order)
        for k in (4, 7):
            mag = max(abs(mp.mpf(J[k].a)), abs(mp.mpf(J[k].b)))
            charge = 4 * width * mag
            sums[k] += charge
            maxima[k] = max(maxima[k], mag)
    payload = {"record": 2865, "status": "FULL_MODEL_REPRICE",
      "cells": cells, "orders": [4,7], "e0": "[1/16,1/8]",
      "sums": {str(k): str(sums[k].b) for k in sums},
      "max_endpoint_norm": {str(k): str(maxima[k]) for k in maxima},
      "nonclaims": ["Lean full-cell enclosure", "ledger domination", "SourceRH", "RH"]}
    OUT.write_text(json.dumps(payload, indent=2) + "\n")
    print(json.dumps(payload, indent=2))

if __name__ == "__main__": main()
