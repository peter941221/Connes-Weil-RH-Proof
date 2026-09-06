"""1217 budget diagnostic (evidence for the sec. 8 floor amendment).

Run 4 died on the sec. 7 gate with budget 7.53e-12 at 16x400 vs
7.12e-12 at 16x200: the budget is FLOOR-dominated (the 1e-13 floors
times the arch weight sums, which grow ~log N near the y -> 0
endpoint where e^{y/2}/(e^y - e^-y) ~ 1/(2y)), not delta-dominated.
Grid refinement cannot help; the floor itself is the binding
constraint.

This script recomputes entry (0,0) on the REGISTERED 16x200 grid and
prints the error-budget DECOMPOSITION with the perr floor removed
(perr_ff(d) = 2 d exactly), next to the floored variant, so the
sec. 8 amendment carries measured numbers:

  * max inner half-rule delta over all required columns,
  * arch-node delta profile (max),
  * floor-free budget: prime_ff + arch_ff + c0-terms_ff + constants,
  * the same with floors 1e-13 / 1e-15,
  * the falsifier-b width requirement (half-width <= ~4.3e-12).
"""
import time

import numpy as np

import mpmath as mp

mp.mp.dps = 45

A = 2
K = 8
PANELS = 16
N_IN = 200
N_OUT = 200
GATE = mp.mpf("1e-12")
CONST_EPS = mp.mpf("1e-14")

L4PG = mp.log(4 * mp.pi) + mp.euler
LT2 = mp.log(mp.tanh(2))
L4PG_ABS = mp.absmax(L4PG)
LT2_ABS = mp.absmax(LT2)


def gauss_legendre(n_per_panel, lo, hi):
    gx, gw = np.polynomial.legendre.leggauss(n_per_panel)
    xs, ws = [], []
    for b in range(PANELS):
        a0 = lo + (hi - lo) * b / PANELS
        a1 = lo + (hi - lo) * (b + 1) / PANELS
        mid = (mp.mpf(a0) + mp.mpf(a1)) / 2
        half = (mp.mpf(a1) - mp.mpf(a0)) / 2
        for g, w in zip(gx, gw):
            xs.append(mid + half * mp.mpf(float(g)))
            ws.append(half * mp.mpf(float(w)))
    return xs, ws


S_X, S_W = gauss_legendre(N_IN, -A, A)
S_XH, S_WH = gauss_legendre(N_IN // 2, -A, A)
Y_X, Y_W = gauss_legendre(N_OUT, 0, 2 * A)
Y_XH, Y_WH = gauss_legendre(N_OUT // 2, 0, 2 * A)

PRIME_POWERS = []
for n in range(2, 54):
    for p in range(2, n + 1):
        if n % p == 0 and all(n % q for q in range(2, p)):
            m2, k = n, 0
            while m2 % p == 0:
                m2 //= p
                k += 1
            if m2 == 1:
                PRIME_POWERS.append((n, mp.log(p), mp.log(n)))
                break
PRIME_POWERS.sort()
NP = len(PRIME_POWERS)
PRIME_W = [lam / mp.sqrt(n) for n, lam, _ in PRIME_POWERS]
NYF = len(Y_X)
IDX0 = 0
IDX_P = 1
IDX_YF = 1 + 2 * NP
IDX_YH = IDX_YF + 2 * NYF


def legendre_vals(k, t):
    if k == 0:
        return mp.mpf(1)
    p0, p1 = mp.mpf(1), t
    for n in range(0, k - 1):
        p0, p1 = p1, ((2 * n + 3) * t * p1 - (n + 1) * p0) / (n + 2)
    return p1


XS_ALL = ([mp.mpf(0)]
          + [ln for _, _, ln in PRIME_POWERS]
          + [-ln for _, _, ln in PRIME_POWERS]
          + list(Y_X) + [-y for y in Y_X]
          + list(Y_XH) + [-y for y in Y_XH])


def build_table(j, s_x, s_w):
    T = []
    for x in XS_ALL:
        col = []
        for s, w in zip(s_x, s_w):
            u = s + x
            if -A < u < A:
                t = u / A
                col.append(w * legendre_vals(j, t)
                           * mp.exp(-1 / (1 - t * t)))
            else:
                col.append(mp.mpf(0))
        T.append(col)
    return T


t0 = time.time()
Tf = build_table(0, S_X, S_W)
Th = build_table(0, S_XH, S_WH)
print(f"tables built {time.time()-t0:.0f}s", flush=True)


def wi_vals(i, s_x):
    return [legendre_vals(i, s / A)
            * (mp.exp(-1 / (1 - (s / A) ** 2)) if abs(s) < A else mp.mpf(0))
            for s in s_x]


def corr_dot(col, wiv):
    acc = mp.mpf(0)
    for wi, cv in zip(wiv, col):
        if wi != 0 and cv != 0:
            acc += wi * cv
    return acc


wiv = wi_vals(0, S_X)
wivh = wi_vals(0, S_XH)
cf = [corr_dot(c, wiv) for c in Tf]
ch = [corr_dot(c, wivh) for c in Th]

inner_max = max(abs(a - b) for a, b in zip(cf, ch))
c0_delta = abs(cf[IDX0] - ch[IDX0])
C0 = cf[IDX0]

prime_ff = mp.mpf(0)
for t in range(NP):
    ip, im = IDX_P + t, IDX_P + NP + t
    prime_ff += PRIME_W[t] * (2 * abs(cf[ip] - ch[ip])
                              + 2 * abs(cf[im] - ch[im]))

arch_ff = mp.mpf(0)
arch_maxdelta = mp.mpf(0)
for t in range(NYF):
    y = Y_X[t]
    ip, im = IDX_YF + t, IDX_YF + NYF + t
    d_pair = abs(cf[ip] - ch[ip]) + abs(cf[im] - ch[im])
    arch_maxdelta = max(arch_maxdelta, d_pair)
    arch_ff += abs(Y_W[t]) * (mp.exp(y / 2) * (2 * d_pair)
                              + 2 * c0_delta) / (mp.exp(y) - mp.exp(-y))
W_SUM_D = sum(abs(w) / (mp.exp(y) - mp.exp(-y))
              for y, w in zip(Y_X, Y_W))
c0_terms_ff = ((L4PG_ABS + LT2_ABS + 2 * W_SUM_D) * 2 * c0_delta)
const_ff = (abs(C0) * 2 * CONST_EPS + L4PG_ABS * CONST_EPS
            + abs(C0) * CONST_EPS + CONST_EPS)


def budget_with_floor(floor):
    def perr(d):
        dd = 2 * d
        return dd if dd > floor else floor
    c0_err = perr(c0_delta)
    arch = mp.mpf(0)
    for t in range(NYF):
        y = Y_X[t]
        ip, im = IDX_YF + t, IDX_YF + NYF + t
        d_pair = abs(cf[ip] - ch[ip]) + abs(cf[im] - ch[im])
        arch += abs(Y_W[t]) * (mp.exp(y / 2) * (2 * perr(d_pair / 2))
                               + 2 * c0_err) / (mp.exp(y) - mp.exp(-y))
    prime = mp.mpf(0)
    for t in range(NP):
        ip, im = IDX_P + t, IDX_P + NP + t
        prime += PRIME_W[t] * (perr(abs(cf[ip] - ch[ip]))
                               + perr(abs(cf[im] - ch[im])))
    return (L4PG_ABS * c0_err + arch + 2 * W_SUM_D * c0_err
            + LT2_ABS * c0_err
            + abs(C0) * 2 * CONST_EPS + L4PG_ABS * CONST_EPS
            + abs(C0) * CONST_EPS + CONST_EPS + prime)


total_ff = prime_ff + arch_ff + c0_terms_ff + const_ff
print(f"=== entry (0,0) @ 16x{N_IN} (registered grid) ===")
print(f"inner max |GL_n - GL_n/2| : {mp.nstr(inner_max, 4)}")
print(f"c0 delta                  : {mp.nstr(c0_delta, 4)}")
print(f"arch node max d_pair      : {mp.nstr(arch_maxdelta, 4)}")
print(f"floor-free budget         : {mp.nstr(total_ff, 5)}")
print(f"  prime_ff  {mp.nstr(prime_ff, 4)}  arch_ff  {mp.nstr(arch_ff, 4)}"
      f"  c0_ff  {mp.nstr(c0_terms_ff, 4)}  const  {mp.nstr(const_ff, 4)}")
print(f"budget @ floor 1e-13      : {mp.nstr(budget_with_floor(mp.mpf('1e-13')), 5)}")
print(f"budget @ floor 1e-15      : {mp.nstr(budget_with_floor(mp.mpf('1e-15')), 5)}")
print(f"gates: sec.7 gate 4e-12 | infl width req half-width <= 4.3e-12")
print(f"value M[0][0] = {mp.nstr(L4PG * C0 + C0 * LT2, 20)} (+arch+prime)")
