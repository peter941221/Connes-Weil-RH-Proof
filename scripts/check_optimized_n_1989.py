#!/usr/bin/env python3
"""Desk study for the optimized-n IBP family (record 1989 prep).

phi_k(u) = exp(-k/s), s = 1 - u^2, |u| < 1; 0 outside; C^1 glued (brick 1),
C^infty on (-1,1).

Structure (hand-derived, F27): phi^(n) = e^{-k/s} B_n with
  B_0 = 1,   B_{n+1} = B_n' + g' * B_n,   g' = -2 k u s^-2,
and B_n is a finite sum of monomials  coeff * k^p * u^a * s^-b  with rational
coeff (exact recursion on dicts; k kept symbolic as a power).

Checks, at 25 dps (quadrature: Gauss-Legendre on saddle-flank-split panels;
|phi^(n)| has kinks at the zeros of B_n, so per-panel convergence tops out
at the percent level for large n — harmless here: an x% value error moves
the c of checks (5)/(6) by x/sqrt(kT) <~ 0.001):
  (1) the recursion reproduces the committed rung-1/2/3 polynomial formulas
      (gevreyDeriv / gevreyDeriv2 / gevreyDeriv3 in the landed bricks)
      EXACTLY as coefficient dicts;
  (2) monomial support size |supp B_n| for n = 1..24 (Lean-architecture
      input: closed-form sum vs operator recursion);
  (3) true total variation N_n(k) = int_{-1}^{1} |phi^(n)| for
      k in {1, 3, 10, 30}, n = 1..48 (measured, not bounded);
  (4) the endpoint-saddle model N_n ~ 2^n Gamma(2n-1) k^(1-n)
      (substitution y = k/s: one layer = 2^(n-1) Gamma(2n-1) k^(1-n),
      both endpoints):
      model/true ratios (claim = the SHAPE, not the constant);
  (5) the vertical optimization inf_n N_n(k)/T^n vs the priced target
      C exp(-c sqrt(k a t)): which c the ladder certifies, at a = 1;
  (6) robustness: same optimization with N_n inflated 100x (stand-in for
      valid-not-sharp Lean constants).

Output: log lines only; acceptance = LOG CONTENTS (log-not-exit-code).
"""
from fractions import Fraction
from mpmath import mp, mpf, exp, quadgl, sqrt as msqrt, gamma as mgamma, log as mlog

mp.dps = 25

# ---------- exact B_n recursion on monomial dicts ----------
# term (a, b, p) -> coeff  meaning  coeff * k^p * u^a * s^(-b),  s = 1 - u^2

def step(B):
    out = {}
    for (a, b, p), c in B.items():
        c = Fraction(c)
        if a >= 1:                      # d/du u^a -> a u^(a-1)
            out[(a - 1, b, p)] = out.get((a - 1, b, p), Fraction(0)) + c * a
        if b >= 1:                      # d/du s^-b -> 2 b u s^-(b+1)   (b=0: s^0 = 1, no chain)
            out[(a + 1, b + 1, p)] = out.get((a + 1, b + 1, p), Fraction(0)) + c * 2 * b
        # g' B term: (-2 k u s^-2) * (c k^p u^a s^-b)
        out[(a + 1, b + 2, p + 1)] = out.get((a + 1, b + 2, p + 1), Fraction(0)) - 2 * c
    return {key: v for key, v in out.items() if v != 0}

def build(nmax):
    Bs = [{(0, 0, 0): Fraction(1)}]
    for _ in range(nmax):
        Bs.append(step(Bs[-1]))
    return Bs

print("=== (1) recursion vs committed rung-1/2/3 polynomial formulas ===")
Bs = build(70)
expected = [
    {(1, 2, 1): Fraction(-2)},
    {(2, 4, 2): Fraction(4), (2, 3, 1): Fraction(-8), (0, 2, 1): Fraction(-2)},
    {(1, 4, 2): Fraction(12), (3, 6, 3): Fraction(-8), (3, 5, 2): Fraction(48),
     (1, 3, 1): Fraction(-24), (3, 4, 1): Fraction(-48)},
]
for n, exp_d in enumerate(expected, start=1):
    ok = Bs[n] == exp_d
    print(f"n={n}: {'PASS' if ok else 'FAIL: got ' + repr(sorted(Bs[n].items()))}")

print("=== (2) monomial support size |supp B_n| (Lean-architecture input) ===")
for n in [1, 2, 3, 4, 6, 8, 12, 16, 20, 24]:
    print(f"n={n:2d}: |supp B_n| = {len(Bs[n])}")

# ---------- 25-dps evaluation of |phi^(n)| ----------

def make_abs_phi(n, k):
    kk = mpf(k)
    terms = [(a, b, p, mpf(c.numerator) / mpf(c.denominator))
             for (a, b, p), c in Bs[n].items()]

    def f(u):
        u = mpf(u)
        s = 1 - u * u
        if abs(u) >= 1 or s <= 0:
            return mpf(0)
        val = sum(c * kk ** p * u ** a * s ** (-b) for (a, b, p, c) in terms)
        return abs(exp(-kk / s) * val)
    return f

def total_variation(n, k):
    f = make_abs_phi(n, k)
    s_star = mpf(k) / (2 * n)           # peak of e^{-k/s} s^{-2n} sits at s = k/(2n)
    grid = [mpf('0.5'), mpf('0.9'), mpf('0.999')]
    if s_star < 1:
        w = msqrt(2 * n)                # y-space half-width dy/y ~ 1/sqrt(2n)
        for s in [s_star * (1 - 1 / w), s_star, s_star * (1 + 1 / w)]:
            if 0 < s < 1:
                grid.append(msqrt(1 - s))
    return 2 * quadgl(f, [mpf(0)] + sorted(set(grid)) + [mpf(1)], maxdegree=5)

print("=== (3) true N_n(k) = int |phi^(n)| (25 dps, quadgl) ===")
Nmeas = {}
for k in [1, 3, 10, 30]:
    for n in range(1, 49):
        Nmeas[(k, n)] = total_variation(n, k)
    row = " ".join(f"n{n}={mp.nstr(Nmeas[(k, n)], 6)}" for n in range(1, 7))
    print(f"k={k:2d}: {row}", flush=True)

print("=== (4) endpoint-saddle model 2^n Gamma(2n-1) k^(1-n): model/true ===")
for k in [1, 3, 10, 30]:
    kk = mpf(k)
    ratios = []
    for n in range(1, 25):
        model = mpf(2) ** n * mgamma(2 * n - 1) * kk ** (1 - n)
        ratios.append(f"n{n}:{mp.nstr(model / Nmeas[(k, n)], 5)}")
    print(f"k={k:2d}: " + " ".join(ratios))

print("=== (5) vertical optimization inf_n N_n(k)/T^n vs priced exp(-c sqrt(kT)) ===")
print("a = 1;  c_ach = -ln(min_n value)/sqrt(kT);  reference c: 0.5 and 0.707")
c707 = 1 / msqrt(2)
for k in [1, 3, 10, 30]:
    kk = mpf(k)
    for T in [mpf('14.1347'), mpf(50), mpf(200), mpf(1000)]:
        best_n, best_v = None, None
        for n in range(1, 49):
            v = Nmeas[(k, n)] / T ** n
            if best_v is None or v < best_v:
                best_n, best_v = n, v
        c_ach = -mlog(best_v) / msqrt(kk * T)
        nstar = msqrt(kk * T / 8)
        print(f"k={k:2d} T={mp.nstr(T, 8):>9}: n*scan={best_n:2d} (saddle n~{mp.nstr(nstar, 4)}): "
              f"val={mp.nstr(best_v, 6)}  c_ach={mp.nstr(c_ach, 5)}  (ref 0.5 / {mp.nstr(c707, 4)})")

print("=== (6) robustness: same with N_n inflated 100x (valid-not-sharp stand-in) ===")
for k in [1, 3, 10, 30]:
    kk = mpf(k)
    for T in [mpf('14.1347'), mpf(50), mpf(200), mpf(1000)]:
        best_n, best_v = None, None
        for n in range(1, 49):
            v = 100 * Nmeas[(k, n)] / T ** n
            if best_v is None or v < best_v:
                best_n, best_v = n, v
        c_ach = -mlog(best_v) / msqrt(kk * T)
        print(f"k={k:2d} T={mp.nstr(T, 8):>9}: n*scan={best_n:2d}  val100={mp.nstr(best_v, 6)}  "
              f"c_ach100={mp.nstr(c_ach, 5)}")

print("=== done ===")
