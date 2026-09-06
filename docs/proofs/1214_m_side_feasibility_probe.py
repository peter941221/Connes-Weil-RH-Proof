"""1214 M-side feasibility probe (record 1146 gap).

Recomputes the gate-matrix entries of the class (2,8) owner INDEPENDENTLY
from the Lean definitions (C1ClassWindowObjects, C1SameOwnerWeil,
C1GateMatrixRepresentation) and measures them against the committed
1112 M_lo/M_hi bundle that backs MLo_q28/MHi_q28.

Lean objects, verbatim:
  classBump x        = exp(-1/(1-x^2)) on |x|<1, else 0
  classWindowFun a i u = P_i(u/a) * classBump(u/a),   a = 2, i = 0..7
  pairTest w i j     = (w i)^involution * (w j)  (convolution)
                       = corr(x) := int w_i(s) w_j(x+s) ds, supp |x| < 4
  ICgate F           = archimedeanTerm F - finitePrimeSum F
  archimedeanTerm F  = (log(4pi)+gamma) F(0)
                       + int_0^inf [e^{y/2}(F(y)+F(-y)) - 2F(0)]/(2 sinh y) dy
  finitePrimeSum F   = sum over prime powers n with nonzero term of
                       Lambda(n)/sqrt(n) * (F(log n) + F(-log n))
Tail beyond the support (y >= 4): integrand = -F(0)/sinh y * ... gives
  exact closed form  + F(0) * log(tanh(2)).
"""
import json

import numpy as np
from numpy.polynomial.legendre import leggauss

mps = None
import mpmath as mp

mp.mp.dps = 40

A = 2.0
K = 8
LOG4PI_GAMMA = float(mp.log(4 * mp.pi) + mp.euler)


def class_bump(x):
    x = np.asarray(x, dtype=float)
    out = np.zeros_like(x)
    m = np.abs(x) < 1.0
    xm = x[m]
    out[m] = np.exp(-1.0 / (1.0 - xm * xm))
    return out


def legendre_vals(i, x):
    # recurrence P0=1, P1=x, (n+2)P_{n+2} = ((2n+3) x P_{n+1} - (n+1) P_n)/(n+2)
    x = np.asarray(x, dtype=float)
    p0 = np.ones_like(x)
    if i == 0:
        return p0
    p1 = x.copy()
    for n in range(0, i - 1):
        p2 = ((2 * n + 3) * x * p1 - (n + 1) * p0) / (n + 2)
        p0, p1 = p1, p2
    return p1


def window(i, u):
    u = np.asarray(u, dtype=float)
    t = u / A
    return legendre_vals(i, t) * class_bump(t)


# --- convolution/correlation C_ij(x) = int w_i(s) w_j(x+s) ds on (-2,2) ---
NQ = 1200
gx, gw = leggauss(NQ)
sx = A * gx            # s nodes in (-2,2)
sw = A * gw
W = np.vstack([window(i, sx) for i in range(K)])   # K x NQ


def corr(i, j, xs):
    xs = np.asarray(xs, dtype=float)
    # w_j(x+s) for each x: evaluate on sx + x
    out = np.empty(len(xs))
    for k, x in enumerate(xs):
        wj = window(j, sx + x)
        out[k] = float(np.sum(sw * W[i] * wj))
    return out


def corr_scalar(i, j, x):
    return float(np.sum(sw * W[i] * window(j, sx + x)))


# prime powers n < e^4 ~ 54.6
PRIME_POWERS = []
for n in range(2, 54):
    m, p, kmax = n, 0, 0
    for p in range(2, n + 1):
        if n % p == 0 and all(n % q for q in range(2, p)):
            k = 0
            m2 = n
            while m2 % p == 0:
                m2 //= p
                k += 1
            if m2 == 1:
                PRIME_POWERS.append((n, float(np.log(p)), np.log(n)))
# (n, Lambda(n)=log p, log n) -- keep unique
seen = set()
PP = []
for n, lam, ln in PRIME_POWERS:
    if n not in seen:
        seen.add(n)
        PP.append((n, lam, ln))
PP.sort()
print(f"visible prime powers ({len(PP)}):", [n for n, _, _ in PP])

# arch quadrature nodes on (0, 4): composite GL
NARC = 16   # panels
NGL = 40    # nodes/panel
ax_gx, ax_gw = leggauss(NGL)
ys = []
ws = []
for b0 in range(NARC):
    lo, hi = 4.0 * b0 / NARC, 4.0 * (b0 + 1) / NARC
    ys.append(lo + (hi - lo) * (ax_gx + 1) / 2)
    ws.append((hi - lo) / 2 * ax_gw)
ys = np.concatenate(ys)
ws = np.concatenate(ws)


def gate(i, j):
    C0 = corr_scalar(i, j, 0.0)
    # arch central part: e^{y/2}(C(y)+C(-y)) - 2 C(0) over 2 sinh y
    cp = corr(i, j, ys)
    cm = corr(i, j, -ys)
    integrand = (np.exp(ys / 2) * (cp + cm) - 2 * C0) / (2 * np.sinh(ys))
    central = float(np.sum(ws * integrand))
    tail = C0 * float(np.log(np.tanh(2.0)))       # exact closed form
    arch = LOG4PI_GAMMA * C0 + central + tail
    prime = 0.0
    for n, lam, ln in PP:
        cn_p = corr_scalar(i, j, ln)
        cn_m = corr_scalar(i, j, -ln)
        prime += lam / np.sqrt(n) * (cn_p + cn_m)
    return arch - prime


# --- committed bundle ---
import os

_cert = None
for cand in (os.path.join(os.path.dirname(os.path.abspath(__file__)),
                          "1112_cert.json"),
             "/home/peter/rh/docs/proofs/1112_cert.json"):
    if os.path.exists(cand):
        _cert = cand
        break
d = json.load(open(_cert))
cls = d["classes"][0]        # A_R = 2 class
from fractions import Fraction


def rat_matrix(rows):
    return np.array([[float(Fraction(v)) for v in row] for row in rows])


M_lo = rat_matrix(cls["M_lo"])
M_hi = rat_matrix(cls["M_hi"])
M_mid = rat_matrix(cls["M_mid"])

print()
print(f"{'i j':>5} {'recomputed':>15} {'1112 M_mid':>15} "
      f"{'diff':>10} {'lo-margin':>10} {'hi-margin':>10}")
worst = 1e9
rows = []
for i in range(K):
    for j in range(i, K):
        g = gate(i, j)
        lo_m = g - M_lo[i][j]
        hi_m = M_hi[i][j] - g
        worst = min(worst, lo_m, hi_m)
        rows.append((i, j, g, M_mid[i][j], g - M_mid[i][j], lo_m, hi_m))
        print(f"{i}{j:>3} {g:+15.9e} {M_mid[i][j]:+15.9e} "
              f"{g - M_mid[i][j]:+10.2e} {lo_m:+10.2e} {hi_m:+10.2e}")

print()
print(f"worst margin across all 36 entries: {worst:.3e}")
print(f"verdict: {'INSIDE all committed boxes' if worst > 0 else 'OUTSIDE some box'}")

# --- 1112-convention recomputation: M = arch + sum 2 Lambda/sqrt(q) C(+xi) ---
print()
print("=== 1112 convention check: arch + prime1112 vs committed M_mid ===")
diffs = []
for i in range(K):
    for j in range(K):
        C0 = corr_scalar(i, j, 0.0)
        cp = corr(i, j, ys)
        cm = corr(i, j, -ys)
        central = float(np.sum(ws * ((np.exp(ys / 2) * (cp + cm) - 2 * C0)
                                     / (2 * np.sinh(ys)))))
        arch = LOG4PI_GAMMA * C0 + central + C0 * float(np.log(np.tanh(2.0)))
        prime1112 = 0.0
        for n, lam, ln in PP:
            prime1112 += 2.0 * lam / np.sqrt(n) * corr_scalar(i, j, ln)
        m1112 = arch + prime1112
        diffs.append(abs(m1112 - M_mid[i][j]))
print(f"max |recomputed_1112 - committed M_mid| over 64 entries: "
      f"{max(diffs):.3e}")
print(f"median: {sorted(diffs)[len(diffs)//2]:.3e}")

# --- Phase 1: gate-convention (arch - prime) bundle viability ---
# V = null space of R (3x8 vanish matrix, s in {0, 0.5, 1}), Gram-whitened;
# question: top eigenvalue of L^-1 Z^T gate Z L^-T < 0 with margin?
print()
print("=== gate-convention bundle on the vanish subspace ===")
VANISH_S = (0.0, 0.5, 1.0)
R = np.empty((3, K))
for si, s in enumerate(VANISH_S):
    for j in range(K):
        R[si, j] = float(np.sum(sw * W[j] * np.exp(s * sx)))
G = np.empty((K, K))
for i in range(K):
    for j in range(K):
        G[i][j] = corr_scalar(i, j, 0.0)
GM = np.empty((K, K))
for i in range(K):
    for j in range(K):
        GM[i][j] = gate(i, j)
u, sv, vh = np.linalg.svd(R, full_matrices=True)
rank_r = int(np.sum(sv > 1e-11 * max(sv[0], 1.0)))
Zn = vh[rank_r:].T
print(f"rank(R) = {rank_r}, dim V = {Zn.shape[1]}")
Pz = Zn.T @ G @ Zn
L = np.linalg.cholesky((Pz + Pz.T) / 2.0)
Li = np.linalg.inv(L)
Hg = Li @ Zn.T @ GM @ Zn @ Li.T
ev = np.linalg.eigvalsh((Hg + Hg.T) / 2.0)
print(f"top(gate|V whitened) = {ev[-1]:+.6e}   (1112 arch+prime had top_mid = "
      f"{cls['top_mid']:+.6e})")
print(f"spectrum: {['%.3e' % v for v in ev[::-1]]}")
# also the arch+prime matrix on V for comparison
M1112 = np.empty((K, K))
for i in range(K):
    for j in range(K):
        C0 = corr_scalar(i, j, 0.0)
        cp = corr(i, j, ys)
        cm = corr(i, j, -ys)
        central = float(np.sum(ws * ((np.exp(ys / 2) * (cp + cm) - 2 * C0)
                                     / (2 * np.sinh(ys)))))
        arch = LOG4PI_GAMMA * C0 + central + C0 * float(np.log(np.tanh(2.0)))
        M1112[i][j] = arch + 2.0 * sum(
            lam / np.sqrt(n) * corr_scalar(i, j, ln) for n, lam, ln in PP)
Hm = Li @ Zn.T @ M1112 @ Zn @ Li.T
evm = np.linalg.eigvalsh((Hm + Hm.T) / 2.0)
print(f"top(arch+prime|V whitened) = {evm[-1]:+.6e}")
