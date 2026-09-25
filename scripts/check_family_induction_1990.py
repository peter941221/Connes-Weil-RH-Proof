#!/usr/bin/env python3
"""Family-brick induction-invariant pre-check (record 1990 prep).

ALL CLOSED-FORM (exact monomial dicts + Gamma sums); the only quadrature is
a small annulus/middle split used to validate the envelope from below.

Machine to certify (hand-derived, F27):
  A_n(k) = (3/5) * sum_terms |c| * k^(p-b+1) * Gamma(b-1)
      is an upper bound for the annulus L1 mass int_{5/6<=|u|<1} |phi^(n)|du
      (y = k/s substitution; 1/(2u) <= 3/5 on u >= 5/6; int e^-y y^(b-2) = G(b-1)).
  Recursion moves on a term (a, b, p, c), weight w(t) = |c| k^(p-b+1) G(b-1):
      move1 d/du u^a:   child weight = a        * w      (a <= n)
      move2 d/du s^-b:  child weight = 2b(b-1)/k * w     (b <= 2n)
      move3 * g' = -2ku/s^2: child = 2b(b-1)/k * w       (G(b+1)=b(b-1)G(b-1))
  => A_{n+1} <= (n + 16 n^2 / k) A_n          (k >= 1: <= 17 n^2 A_n)
  => envelope A_n <= A_1 * prod_{j=1}^{n-1} (j + 16 j^2 / k),  A_1 <= e^{-36k/11}.
  Middle (11/36 <= s <= 1, two rings):
      M_n <= e^{-2k} (7/36) sum|c| k^p 2^b  +  e^{-k} (1/2) sum|c| k^p (36/11)^b.
  Consumer: inf_n (envA_n + envM_n)/T^n  vs the priced exp(-c sqrt(kT)).

Checks:
  (1) invariants over B_n, n = 1..40: max a, min/max b, max p, min(b-p),
      min b (need >= 2 for Gamma(b-1)), parity of a (== n mod 2);
  (2) step ratios A_{n+1}/A_n measured vs the bound (n + 16 n^2/k);
      report the effective rho (A-ratio ~ rho n^2) that sets c = 1/sqrt(rho);
  (3) envelope check: prod-bound >= measured A_n for n up to 30;
  (4) envelope >= truth: (A_n + M_n) vs the 1989-style total mass
      (quadgl split annulus/middle at |u| = 5/6, n = 1..12, k in {1,3,10,30});
  (5) consumer: c_ach of the MACHINE envelope on the 1989 T-grid; compare
      with the true-mass c_ach from record 1989.

Output: log lines only; acceptance = LOG CONTENTS (log-not-exit-code).
"""
from fractions import Fraction
from mpmath import mp, mpf, exp, quadgl, sqrt as msqrt, gamma as mgamma, log as mlog

mp.dps = 40

# ---------- exact B_n recursion on monomial dicts (verified vs 1989) ----------

def step(B):
    out = {}
    for (a, b, p), c in B.items():
        c = Fraction(c)
        if a >= 1:
            out[(a - 1, b, p)] = out.get((a - 1, b, p), Fraction(0)) + c * a
        if b >= 1:
            out[(a + 1, b + 1, p)] = out.get((a + 1, b + 1, p), Fraction(0)) + c * 2 * b
        out[(a + 1, b + 2, p + 1)] = out.get((a + 1, b + 2, p + 1), Fraction(0)) - 2 * c
    return {key: v for key, v in out.items() if v != 0}

NMAX = 70
Bs = [{(0, 0, 0): Fraction(1)}]
for _ in range(NMAX):
    Bs.append(step(Bs[-1]))

print("=== (1) invariants over B_n ===")
# EXACT identity (move-count argument): with s1+s2+s3 = n the moves,
#   a = n - 2 s1  and  b - p = n - s1  =>  b - p = (n + a)/2  per term.
bad = 0
for n in range(1, NMAX + 1):
    terms = Bs[n]
    mx_a = max(a for (a, b, p) in terms)
    mn_b = min(b for (a, b, p) in terms)
    mx_b = max(b for (a, b, p) in terms)
    mx_p = max(p for (a, b, p) in terms)
    ident_ok = all(b - p == (n + a) // 2 and (n + a) % 2 == 0 for (a, b, p) in terms)
    ok = (mx_a <= n) and (mn_b >= 2) and (mx_b <= 2 * n) and (mx_p <= n) and ident_ok
    if not ok:
        bad += 1
        print(f"n={n}: INVARIANT VIOLATION a_max={mx_a} b_min={mn_b} b_max={mx_b} "
              f"p_max={mx_p} identity_ok={ident_ok}")
    if n in (1, 2, 3, 4, 8, 16, 24, 32, 40):
        print(f"n={n:2d}: a<={mx_a}  2<=b<={mx_b}(2n={2*n})  p<={mx_p}  "
              f"b-p=(n+a)/2 ok={ident_ok}  |supp|={len(terms)}")
print("invariants:", "PASS" if bad == 0 else f"FAIL ({bad} rows)")

# ---------- exact A_n(k): annulus envelope ----------

def A_exact(n, k):
    kk = mpf(k)
    s = mpf(0)
    for (a, b, p), c in Bs[n].items():
        if b < 2:
            continue
        s += abs(mpf(c.numerator) / mpf(c.denominator)) * kk ** (p - b + 1) * mgamma(b - 1)
    return mpf(3) / 5 * s

def A1_bound(k):
    # A_1 <= (3/5) * 2k * Gamma(1) * int_{5/6}^1 e^{-k/s} du <= (1/5) k * ... use e^{-36k/11}/5 * ... :
    # exact: |phi'| = 2ku/s^2 e^{-k/s} <= 2k (36/11)^2 e^{-36k/11} on the annulus, width 1/6*2 = 1/3
    return mpf(2) * mpf(k) * (mpf(36) / 11) ** 2 * exp(-mpf(36) * mpf(k) / 11) / 3

print("=== (2) step ratios A_{n+1}/A_n vs bound (n + 16 n^2/k) ===")
print("effective rho from ratio ~ rho n^2 at n=12: sets certified c = 1/sqrt(rho)")
for k in [1, 3, 10, 30]:
    kk = mpf(k)
    ratios = []
    for n in range(1, 24):
        r = A_exact(n + 1, k) / A_exact(n, k)
        bound = n + 16 * n * n / kk
        ratios.append((n, r, bound))
    row = " ".join(f"n{n}:{mp.nstr(r, 4)}/{mp.nstr(bd, 5)}" for (n, r, bd) in ratios[:8])
    all_ok = all(r <= bd for (n, r, bd) in ratios)
    r12 = ratios[11][1]
    rho12 = r12 / 144
    print(f"k={k:2d}: {row}")
    print(f"       machine-bound holds: {'PASS' if all_ok else 'FAIL'};  "
          f"rho(n=12)={mp.nstr(rho12, 4)} -> c ~ {mp.nstr(1 / msqrt(rho12), 4)}")

print("=== (3) closed envelope prod (j + 16 j^2/k) >= A_n ===")
for k in [1, 3, 10, 30]:
    kk = mpf(k)
    env = A_exact(1, k)                 # base = the functional itself at n=1
    ok = True
    worst = mpf(0)
    for n in range(1, 31):
        if n > 1:
            env = env * ((n - 1) + 16 * (n - 1) ** 2 / kk)
        r = A_exact(n, k) / env
        worst = max(worst, r)
        if r > 1:
            ok = False
    print(f"k={k:2d}: envelope >= A_n for n<=30: {'PASS' if ok else 'FAIL'}  "
          f"worst A_n/env = {mp.nstr(worst, 4)}")

# ---------- annulus/middle split by quadgl (validation of (A_n + M_n) >= truth) ----------

def make_abs_phi(n, k):
    kk = mpf(k)
    terms = [(a, b, p, mpf(c.numerator) / mpf(c.denominator))
             for (a, b, p), c in Bs[n].items()]

    def f(u):
        u = mpf(u)
        s = 1 - u * u
        if abs(u) >= 1 or s <= 0:
            return mpf(0)
        val = mpf(0)
        for a, b, p, c in terms:
            val += c * kk ** p * u ** a * s ** (-b)
        return abs(exp(-kk / s) * val)
    return f

def split_mass(n, k):
    f = make_abs_phi(n, k)
    s_star = mpf(k) / (2 * n)
    grid = [mpf('0.5'), mpf('0.8'), mpf('0.9'), mpf('0.999')]
    if s_star < 1:
        w = msqrt(2 * n)
        for s in [s_star * (1 - 1 / w), s_star, s_star * (1 + 1 / w)]:
            if 0 < s < 1:
                grid.append(mpf('5') / 6)
                grid.append(msqrt(1 - s))
    grid = sorted(set(grid))
    ann = 2 * quadgl(f, [mpf(5) / 6] + [g for g in grid if g > mpf(5) / 6] + [mpf(1)], maxdegree=5)
    tot = 2 * quadgl(f, [mpf(0)] + grid + [mpf(1)], maxdegree=5)
    return ann, tot

def M_exact(n, k):
    kk = mpf(k)
    low = mpf(0)
    high = mpf(0)
    for (a, b, p), c in Bs[n].items():
        ac = abs(mpf(c.numerator) / mpf(c.denominator)) * kk ** p
        low += ac * mpf(2) ** b
        high += ac * (mpf(36) / 11) ** b
    return exp(-2 * kk) * mpf(7) / 36 * low + exp(-kk) / 2 * high

print("=== (4) (A_n + M_n) >= measured total mass (quadgl, n=1..12) ===")
allok = True
for k in [1, 3, 10, 30]:
    worst = mpf(0)
    for n in range(1, 13):
        ann, tot = split_mass(n, k)
        bound = A_exact(n, k) + M_exact(n, k)
        ratio = tot / bound
        worst = max(worst, ratio)
        if ratio > 1:
            allok = False
            print(f"  VIOLATION k={k} n={n}: truth/bound = {mp.nstr(ratio, 6)}")
    print(f"k={k:2d}: worst truth/(A+M) = {mp.nstr(worst, 5)}  "
          f"{'PASS' if worst <= 1 else 'FAIL'}")
print("envelope >= truth:", "PASS" if allok else "FAIL")

print("=== (5) consumer: machine envelope on the 1989 T-grid ===")
for k in [1, 3, 10, 30]:
    kk = mpf(k)
    envs = []
    env = A_exact(1, k)                 # base = the functional itself at n=1
    for n in range(1, 65):
        if n > 1:
            env = env * ((n - 1) + 16 * (n - 1) ** 2 / kk)
        envs.append(env + M_exact(n, k))
    for T in [mpf('14.1347'), mpf(50), mpf(200), mpf(1000)]:
        best_n, best_v = None, None
        for n in range(1, 65):
            v = envs[n - 1] / T ** n
            if best_v is None or v < best_v:
                best_n, best_v = n, v
        c_ach = -mlog(best_v) / msqrt(kk * T)
        print(f"k={k:2d} T={mp.nstr(T, 8):>9}: n*={best_n:2d}  c_env={mp.nstr(c_ach, 5)}")
print("=== done ===")
