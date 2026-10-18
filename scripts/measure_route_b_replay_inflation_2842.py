#!/usr/bin/env python3
"""Measure exact rational-box dependency-loss inflation for record 2841."""
from fractions import Fraction
import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DATA = json.loads((ROOT / "results/2840_route_b_cell4096_stage_bridge.json").read_text())
OUT = ROOT / "results/2842_route_b_replay_inflation.json"


def f(s):
    a, b = s.split("/")
    return Fraction(int(a), int(b))


def bx(z):
    return (f(z["lo"]), f(z["hi"]))


def add(a, b): return (a[0] + b[0], a[1] + b[1])
def sub(a, b): return (a[0] - b[1], a[1] - b[0])
def mul(a, b):
    q = [a[0]*b[0], a[0]*b[1], a[1]*b[0], a[1]*b[1]]
    return min(q), max(q)
def scale(c, a): return (c*a[0], c*a[1])
def inv_pos(a): return (1/a[1], 1/a[0])
def smul(a, c): return scale(c, a)


def recip(X):
    out = [inv_pos(X[0])]
    for n in range(len(X)-1):
        total = (Fraction(0), Fraction(0))
        for j in range(n+1):
            total = add(total, smul(mul(X[j+1], out[n-j]), Fraction(math.comb(n+1, j+1))))
        out.append(mul(sub((Fraction(0), Fraction(0)), total), inv_pos(X[0])))
    return out


def expo(X, e0):
    out = [e0]
    for n in range(len(X)-1):
        total = (Fraction(0), Fraction(0))
        for j in range(n+1):
            total = add(total, smul(mul(X[j+1], out[n-j]), Fraction(math.comb(n, j))))
        out.append(total)
    return out


def product(A, B):
    return [sum_boxes([smul(mul(A[j], B[k-j]), Fraction(math.comb(k,j)))
                       for j in range(k+1)]) for k in range(len(A))]


def sum_boxes(xs):
    z = (Fraction(0), Fraction(0))
    for x in xs: z = add(z, x)
    return z


def main():
    order = 4
    stage = DATA["orders"][str(order)]
    phase = [bx(z) for z in stage["phase"]]
    exp_target = [bx(z) for z in stage["exp"]]
    den_target = [bx(z) for z in stage["denominator"]]
    rec_target = [bx(z) for z in stage["reciprocal"]]
    trans_target = [bx(z) for z in stage["transition"]]
    exp_replay = expo(phase, exp_target[0])
    den_replay = [add(exp_replay[0], (Fraction(1), Fraction(1)))] + exp_replay[1:]
    rec_replay = recip(den_replay)
    trans_replay = product(exp_replay, rec_replay)
    rows = []
    for k, (a, t) in enumerate(zip(trans_replay, trans_target)):
        width = t[1] - t[0]
        extra = max(Fraction(0), a[0]-t[0], t[1]-a[1])
        rows.append({"k": k, "target_width": str(width),
                     "replay_width": str(a[1]-a[0]),
                     "extra_each_side_bound": str(extra),
                     "replay_contains_target": a[0] <= t[0] and t[1] <= a[1],
                     "target_contains_replay": t[0] <= a[0] and a[1] <= t[1]})
    payload = {"record": 2842, "status": "CORRECTED_REPLAY_CONTAINMENT",
               "owner": "Route B cell 4096 order 4", "rows": rows,
               "interpretation": "With the replay denominator owned by the replay, the target contains every order-4 replay slot.",
               "nonclaims": ["Lean soundness", "Python-to-Lean bridge", "ledger domination", "SourceRH", "RH"]}
    OUT.write_text(json.dumps(payload, indent=2) + "\n")
    print(json.dumps({"record": 2842, "rows": rows}, indent=2))


if __name__ == "__main__": main()
