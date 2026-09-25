#!/usr/bin/env python3
"""Check the hand derivation for brick-2 rung 2 (record 1987 prep).

Verifies, at k in {1, 3, 30}:
  (1) phi'' formula  f*(-2k s^-2 + 4 k^2 u^2 s^-4 - 8 k u^2 s^-3), s = 1-u^2
  (2) phi'' >= 0 on (5/6, 1)   (antitone-outer precondition)
  (3) int_{5/6}^1 phi'' du = -phi'(5/6) = (2160 k/121) e^{-36k/11}
  (4) total int_{-1}^1 |phi''| <= (532 k^2 + 398 k) e^{-k}
  (5) middle pointwise: |phi''| <= e^{-k} (22k + 195k + 319 k^2) on |u| <= 5/6
  (6) rung-1 constants reproduce: int |phi'| = 2 e^{-4k/3} + (16k/9) e^{-k}
Output: log lines only; acceptance = LOG CONTENTS (log-not-exit-code).
"""
from mpmath import mp, mpf, exp, diff, quad

mp.dps = 40

def phi(u, k):
    if abs(u) >= 1:
        return mpf(0)
    return exp(-k / (1 - u * u))

def d2_formula(u, k):
    s = 1 - u * u
    f = exp(-k / s)
    return f * (-2 * k / s**2 + 4 * k * k * u * u / s**4 - 8 * k * u * u / s**3)

def d1_formula(u, k):
    s = 1 - u * u
    return exp(-k / s) * (-2 * k * u / (s * s))

print("=== (1) phi'' formula vs numerical second derivative ===")
for k in [1, 3, 30]:
    for u in [-0.9, -0.5, -0.2, 0.1, 0.5, 0.83]:
        num = diff(lambda v: phi(v, k), mpf(u), 2)
        form = d2_formula(mpf(u), mpf(k))
        rel = abs(num - form) / abs(form)
        print(f"k={k:2d} u={u:5}: num={mp.nstr(num, 12)} form={mp.nstr(form, 12)} rel={mp.nstr(rel, 3)}")

print("=== (2) phi'' >= 0 on (5/6, 1) ===")
ok2 = True
for k in [1, 3, 30]:
    for i in range(1, 60):
        u = mpf(5) / 6 + (1 - mpf(5) / 6) * i / 60
        if d2_formula(u, mpf(k)) < 0:
            ok2 = False
            print(f"VIOLATION k={k} u={mp.nstr(u, 8)}")
print("antitone-outer precondition:", "PASS" if ok2 else "FAIL")

print("=== (3) int_{5/6}^1 phi'' = (2160k/121) e^{-36k/11} ===")
for k in [1, 3, 30]:
    kk = mpf(k)
    lhs = quad(lambda v: d2_formula(v, kk), [mpf(5) / 6, 1])
    rhs = mpf(2160) * kk / 121 * exp(-36 * kk / 11)
    rel = abs(lhs - rhs) / rhs
    print(f"k={k:2d}: lhs={mp.nstr(lhs, 12)} rhs={mp.nstr(rhs, 12)} rel={mp.nstr(rel, 3)}")

print("=== (4) total int |phi''| <= (532 k^2 + 398 k) e^{-k} ===")
for k in [1, 3, 30]:
    kk = mpf(k)
    lhs = quad(lambda v: abs(d2_formula(v, kk)), [-1, 0, 1])
    rhs = (532 * kk**2 + 398 * kk) * exp(-kk)
    print(f"k={k:2d}: total={mp.nstr(lhs, 8)} bound={mp.nstr(rhs, 8)} ratio={mp.nstr(lhs / rhs, 4)}  {'PASS' if lhs <= rhs else 'FAIL'}")

print("=== (5) middle pointwise |phi''| <= e^{-k}(22k + 195k + 319k^2), |u|<=5/6 ===")
ok5 = True
for k in [1, 3, 30]:
    kk = mpf(k)
    bound = exp(-kk) * (22 * kk + 195 * kk + 319 * kk * kk)
    for i in range(0, 101):
        u = -mpf(5) / 6 + 2 * (mpf(5) / 6) * i / 100
        if abs(d2_formula(u, kk)) > bound:
            ok5 = False
            print(f"VIOLATION k={k} u={mp.nstr(u, 8)}")
print("middle pointwise:", "PASS" if ok5 else "FAIL")

print("=== (6) rung-1 reproduction: int |phi'| = 2 e^{-4k/3} + (16k/9) e^{-k} ===")
for k in [1, 3, 30]:
    kk = mpf(k)
    lhs = quad(lambda v: abs(diff(lambda w: phi(w, kk), v)), [-1, 0, 1])
    rhs = 2 * exp(-4 * kk / 3) + 16 * kk / 9 * exp(-kk)
    rel = abs(lhs - rhs) / rhs
    print(f"k={k:2d}: lhs={mp.nstr(lhs, 10)} rhs={mp.nstr(rhs, 10)} rel={mp.nstr(rel, 3)}")
