#!/usr/bin/env python3
"""Check the hand derivation for brick-2 rung 3 (record 1988 prep).

phi'''(u) = e^{-k/s} * (12 k^2 u s^-4 - 8 k^3 u^3 s^-6 + 48 k^2 u^3 s^-5
                        - 24 k u s^-3 - 48 k u^3 s^-4),  s = 1 - u^2.

Verifies, at k in {1, 3, 30}:
  (1) phi''' formula vs numerical third derivative
  (2) middle pointwise |phi'''| <= e^{-k} (9500 k^3 + 19400 k^2 + 6500 k)
      on |u| <= 5/6
  (3) outer pointwise (7-power trade) on 5/6 <= |u| < 1:
      |phi'''| <= 7^7 (12 k^-5 s^3 + 8 k^-4 u^2 s + 48 k^-5 u^2 s^2
                       + 24 k^-6 s^4 + 48 k^-6 u^2 s^3)
  (4) total int_{-1}^1 |phi'''| <= (5/3) mid + (1/3) 7^7 (8k^-4 + 60k^-5 + 72k^-6)
  (5) DOCUMENTS the sign flip of phi''' on [5/6, 1) at k = 1 (why the
      rung-2 FTC-exact outer mass trick is dropped for rung 3)
Output: log lines only; acceptance = LOG CONTENTS (log-not-exit-code).
"""
from mpmath import mp, mpf, exp, diff, quad

mp.dps = 40

def phi(u, k):
    if abs(u) >= 1:
        return mpf(0)
    return exp(-k / (1 - u * u))

def d3_formula(u, k):
    s = 1 - u * u
    f = exp(-k / s)
    return f * (12 * k * k * u / s**4 - 8 * k**3 * u**3 / s**6
                + 48 * k * k * u**3 / s**5 - 24 * k * u / s**3
                - 48 * k * u**3 / s**4)

SEVEN = mpf(7) ** 7

print("=== (1) phi''' formula vs numerical third derivative ===")
for k in [1, 3, 30]:
    for u in [-0.9, -0.5, -0.2, 0.1, 0.5, 0.83]:
        num = diff(lambda v: phi(v, k), mpf(u), 3)
        form = d3_formula(mpf(u), mpf(k))
        if form == 0:
            print(f"k={k:2d} u={u:5}: both ~0")
            continue
        rel = abs(num - form) / abs(form)
        print(f"k={k:2d} u={u:5}: num={mp.nstr(num, 12)} form={mp.nstr(form, 12)} rel={mp.nstr(rel, 3)}")

print("=== (2) middle pointwise |phi'''| <= e^{-k}(9500k^3 + 19400k^2 + 6500k), |u|<=5/6 ===")
ok2 = True
for k in [1, 3, 30]:
    kk = mpf(k)
    bound = exp(-kk) * (9500 * kk**3 + 19400 * kk**2 + 6500 * kk)
    for i in range(0, 101):
        u = -mpf(5) / 6 + 2 * (mpf(5) / 6) * i / 100
        if abs(d3_formula(u, kk)) > bound:
            ok2 = False
            print(f"VIOLATION k={k} u={mp.nstr(u, 8)}")
print("middle pointwise:", "PASS" if ok2 else "FAIL")

print("=== (3) outer pointwise 7-trade bound, 5/6 <= |u| < 1 ===")
ok3 = True
for k in [1, 3, 30]:
    kk = mpf(k)
    for i in range(60):
        u = mpf(5) / 6 + (1 - mpf(5) / 6) * i / 60
        for uu in [u, -u]:
            s = 1 - uu * uu
            trade = (SEVEN * (12 * kk**-5 * s**3 + 8 * kk**-4 * uu**2 * s
                              + 48 * kk**-5 * uu**2 * s**2
                              + 24 * kk**-6 * s**4
                              + 48 * kk**-6 * uu**2 * s**3))
            if abs(d3_formula(uu, kk)) > trade:
                ok3 = False
                print(f"VIOLATION k={k} u={mp.nstr(uu, 8)}")
print("outer pointwise:", "PASS" if ok3 else "FAIL")

print("=== (4) total int |phi'''| <= (5/3)mid + (1/3)7^7(8k^-4+60k^-5+72k^-6) ===")
for k in [1, 3, 30]:
    kk = mpf(k)
    lhs = quad(lambda v: abs(d3_formula(v, kk)), [-1, 0, 1])
    mid = exp(-kk) * (9500 * kk**3 + 19400 * kk**2 + 6500 * kk) * mpf(5) / 3
    out = SEVEN * (8 * kk**-4 + 60 * kk**-5 + 72 * kk**-6) * mpf(1) / 3
    rhs = mid + out
    print(f"k={k:2d}: total={mp.nstr(lhs, 8)} bound={mp.nstr(rhs, 8)} ratio={mp.nstr(lhs / rhs, 4)}  {'PASS' if lhs <= rhs else 'FAIL'}")

print("=== (5) phi''' sign flip on [5/6, 1) at k = 1 (documents dropping FTC-exact) ===")
for k in [1]:
    kk = mpf(k)
    for i in range(0, 6):
        u = mpf(5) / 6 + (1 - mpf(5) / 6) * i / 6
        print(f"k={k} u={mp.nstr(u, 6)}: phi''' = {mp.nstr(d3_formula(u, kk), 10)}")
