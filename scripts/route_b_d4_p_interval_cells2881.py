"""Outward interval-cell screen for the owner-correlated D4 derivative P."""
import json
from pathlib import Path
import mpmath as mp
from mpmath import iv
import sympy as s

mp.iv.dps = 40
t, z, u, q = s.symbols("t z u q")
phi = 1 / u - 1 / (1 - u)
velocity = -s.diff(phi, u) * q * (1 - q)
jet = q
for _ in range(4):
    jet = s.factor(s.diff(jet, u) + s.diff(jet, q) * velocity)
num, _ = s.fraction(jet)
h = s.factor(num.subs({u: (1 + t) / 2, q: (1 + t * z) / 2}) /
            (t * (t * z - 1) * (t * z + 1)))
zp = (2 * (1 + t**2) * (1 - t**2 * z**2) / (1 - t**2)**2 - z) / t
n, _ = s.fraction(s.factor(s.diff(h, t) + s.diff(h, z) * zp))
poly = s.Poly(s.factor(-n / 2), t, z)
TERMS = [(int(i), int(j), int(c)) for (i, j), c in poly.terms()]


def z_of(x):
    return mp.tanh(2 * x / (1 - x * x)) / x if x else mp.mpf(2)


def p_interval(a, b, za, zb):
    x = iv.mpf([a, b])
    y = iv.mpf([min(za, zb), max(za, zb)])
    total = iv.mpf([0, 0])
    for i, j, c in TERMS:
        total += iv.mpf(c) * x**i * y**j
    return total


def main():
    regions = [(mp.mpf(1) / 4096, mp.mpf("0.1353"), "negative"),
               (mp.mpf("0.3029"), mp.mpf("0.4999"), "positive")]
    rows = []
    for left, right, expected in regions:
        t0, t1 = 2 * left - 1, 2 * right - 1
        certified = 0
        undecided = 0
        for k in range(200):
            a = t0 + (t1 - t0) * k / 200
            b = t0 + (t1 - t0) * (k + 1) / 200
            value = p_interval(a, b, z_of(a), z_of(b))
            if (expected == "negative" and value.b < 0) or (expected == "positive" and value.a > 0):
                certified += 1
            else:
                undecided += 1
        rows.append({"u_left": str(left), "u_right": str(right),
                     "expected_sign": expected, "cells": 200,
                     "certified": certified, "undecided": undecided})
    payload = {"record": 2881, "rows": rows,
               "claims": {"outward_interval_cell_screen": True,
                          "global_sign_certificate": False},
               "next_target": "reduce undecided cells with Taylor correlation bounds"}
    out = Path("results/2881_route_b_d4_p_interval_cells.json")
    out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
