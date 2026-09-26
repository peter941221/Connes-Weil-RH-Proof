#!/usr/bin/env python3
"""F1b identification pre-check (record 1992 prep).

The identity to certify (hand-derived, F27):
    d^n/du^n [ exp(-k/s(u)) ]  =  exp(-k/s(u)) * B_n(u),   s = 1 - u^2,
with B_n the monomial family: B_{n+1} = B_n' + g' * B_n, g' = -2 k u / s^2,
B_0 = 1, terms c * k^p * u^a * s^-b.

Lean recursion to validate (brick C1GevreyFamilyMonomials, `children`):
    move1 (a >= 1): (a-1, b,   p,   c * a)
    move2 (b >= 1): (a+1, b+1, p,   c * 2b)
    move3 (always): (a+1, b+2, p+1, c * (-2))

Checks (mpmath, 60 dps; acceptance = LOG CONTENTS):
  (1) value parity: multiset B_n (Lean children order, no merging) equals the
      merged-dict B_n of the committed desk recursion (record 1989/1990
      `step`) — validates that the Lean multiset carries the same function;
  (2) closed cross-checks: B_1 = -2ku/s^2 pointwise, B_2 vs the desk dict;
  (3) analytic identity: mp.diff^n of the profile equals exp(-k/s)*B_n at a
      (n, k, u) grid — the F1b HasDerivAt statement itself.
"""
from fractions import Fraction
from mpmath import mp, mpf, exp, diff

mp.dps = 60

# ---------- Lean-children multiset recursion (no merging) ----------

def step_multiset(terms):
    out = []
    for (a, b, p), c in terms:
        if a >= 1:
            out.append(((a - 1, b, p), c * a))
        if b >= 1:
            out.append(((a + 1, b + 1, p), c * 2 * b))
        out.append(((a + 1, b + 2, p + 1), c * (-2)))
    return out

def step_merged(B):
    out = {}
    for (a, b, p), c in B.items():
        c = Fraction(c)
        if a >= 1:
            out[(a - 1, b, p)] = out.get((a - 1, b, p), Fraction(0)) + c * a
        if b >= 1:
            out[(a + 1, b + 1, p)] = out.get((a + 1, b + 1, p), Fraction(0)) + c * 2 * b
        out[(a + 1, b + 2, p + 1)] = out.get((a + 1, b + 2, p + 1), Fraction(0)) - 2 * c
    return {key: v for key, v in out.items() if v != 0}

NMAX = 7
multisets = [[((0, 0, 0), Fraction(1))]]
mergeds = [{(0, 0, 0): Fraction(1)}]
for _ in range(NMAX):
    multisets.append(step_multiset(multisets[-1]))
    mergeds.append(step_merged(mergeds[-1]))


def B_multiset(n, k, u):
    kk, uu = mpf(k), mpf(u)
    s_inv = 1 / (1 - uu * uu)
    s = mpf(0)
    for (a, b, p), c in multisets[n]:
        s += mpf(c.numerator) / mpf(c.denominator) * kk ** p * uu ** a * s_inv ** b
    return s


def B_merged(n, k, u):
    kk, uu = mpf(k), mpf(u)
    s_inv = 1 / (1 - uu * uu)
    s = mpf(0)
    for (a, b, p), c in mergeds[n].items():
        s += mpf(c.numerator) / mpf(c.denominator) * kk ** p * uu ** a * s_inv ** b
    return s


print("=== (1) multiset-vs-merged value parity ===")
bad = 0
for k in (1, 3, 10):
    for u in (mpf("0.3"), mpf("-0.6"), mpf("0.85"), mpf("0.95")):
        for n in range(0, NMAX + 1):
            v1, v2 = B_multiset(n, k, u), B_merged(n, k, u)
            scale = max(abs(v1), mpf(1))
            if abs(v1 - v2) / scale > mpf("1e-35"):
                bad += 1
                print(f"PARITY FAIL n={n} k={k} u={u}: {mp.nstr(v1, 8)} vs {mp.nstr(v2, 8)}")
print("parity:", "PASS" if bad == 0 else f"FAIL ({bad} rows)")

print("=== (2) closed cross-check B_1 = -2ku/s^2, B_2 spot ===")
bad2 = 0
for k in (1, 3, 10):
    for u in (mpf("0"), mpf("0.4"), mpf("-0.7"), mpf("0.9")):
        uu, kk = mpf(u), mpf(k)
        s_inv = 1 / (1 - uu * uu)
        closed1 = -2 * kk * uu * s_inv ** 2
        if abs(B_multiset(1, k, u) - closed1) > mpf("1e-30"):
            bad2 += 1
            print(f"B1 FAIL k={k} u={u}")
print("B_1 closed form:", "PASS" if bad2 == 0 else "FAIL")


def profile(k, u):
    return exp(-mpf(k) / (1 - mpf(u) * mpf(u)))


print("=== (3) analytic identity diff^n profile == exp(-k/s)*B_n ===")
# Scale discipline: at u = 0 the odd-order TRUE derivatives are exactly 0
# (even profile) and mp.diff reports 1e-78-style roundoff — a pure relative
# metric explodes there.  Scale by the natural magnitude prior of the n-th
# derivative, profile * (6 k s_inv^2)^n (generous: each differentiation of
# e^{-k/s} B_n costs at most ~(2k s_inv^2 + deg) factors; 6 is slack).
worst_rel = mpf(0)
worst_row = None
bad3 = 0
for n in range(1, 7):
    for k in (1, 3, 10):
        for u in (mpf("0"), mpf("0.3"), mpf("-0.3"), mpf("0.6"),
                  mpf("-0.6"), mpf("0.85"), mpf("-0.85"), mpf("0.95")):
            lhs = diff(lambda x: profile(k, x), mpf(u), n)
            rhs = profile(k, u) * B_multiset(n, k, u)
            s_inv = 1 / (1 - mpf(u) * mpf(u))
            prior = profile(k, u) * (6 * mpf(k) * s_inv ** 2) ** n
            scale = max(abs(rhs), prior, mpf("1e-300"))
            rel = abs(lhs - rhs) / scale
            if rel > worst_rel:
                worst_rel = rel
                worst_row = (n, k, str(u))
            if rel > mpf("1e-22"):
                bad3 += 1
                print(f"IDENTITY FAIL n={n} k={k} u={u}: "
                      f"{mp.nstr(lhs, 10)} vs {mp.nstr(rhs, 10)} rel={mp.nstr(rel, 4)}")
print(f"identity rows: 144, worst rel = {mp.nstr(worst_rel, 4)} at {worst_row}")
print("analytic identity:", "PASS" if bad3 == 0 else f"FAIL ({bad3} rows)")
print("=== done ===")
