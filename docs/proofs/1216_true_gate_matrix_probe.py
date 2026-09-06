"""1216 probe: the TRUE Lean gateMatrix on the (2,8) class owner.

Record 1214 F2/F3 mis-stated the Lean gate convention: the verbatim
definition (C1LocalConfigurationDomination, `ICgate F :=
archimedeanTerm F + finitePrimeSum F`) is arch PLUS prime, and the
prime readout is BOTH-SIDED:  Lambda(n)/sqrt(n) * (F(log n) + F(-log n)).
The 1214 probe computed arch MINUS prime (single-sided prime) -- a
phantom matrix; its +1.713 whitened top does not describe gateMatrix.

This probe computes the TRUE matrix
    M_true[i,j] = arch(i,j) + sum_n Lambda/sqrt(n) (C_ij(+ln) + C_ij(-ln))
on the class (2,8) family from the Lean definitions and measures:
  (1) same-parity entries vs the committed 1112 M_mid (must match:
      both-sides = 2 * single-sided when C(-x) = +C(x));
  (2) mixed-parity entries (predicted EXACT 0 up to quadrature noise;
      D1 parity lemma);
  (3) Gram-whitened top eigenvalue on V = ker R (dim 5) -- the number
      that decides whether the 1112 margin architecture (U ~ -1.04e-6)
      survives on the true matrix.

Lean objects, verbatim:
  classWindowFun a i u = P_i(u/a) * exp(-1/(1-(u/a)^2)) on |u/a| < 1
  pairTest w i j       = (w i)^involution * (w j):  C_ij(x) :=
                       int w_i(s) w_j(x+s) ds,  supp |x| < 2a = 4
  ICgate F             = archimedeanTerm F + finitePrimeSum F
  archimedeanTerm F    = (log(4pi)+gamma) F(0)
                       + int_0^inf [e^{y/2}(F(y)+F(-y)) - 2F(0)]/(e^y-e^-y) dy
                       (tail beyond y = 4: F(0) log tanh(2), exact)
  finitePrimeSum F     = sum over visible prime powers n of
                       Lambda(n)/sqrt(n) * (F(log n) + F(-log n))
"""
import json
import os
from fractions import Fraction

import numpy as np
from numpy.polynomial.legendre import leggauss

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
    return legendre_vals(i, u / A) * class_bump(u / A)


# --- correlation quadrature: C_ij(x) = int_{-2}^{2} w_i(s) w_j(x+s) ds ---
NQ = 1200
gx, gw = leggauss(NQ)
sx = A * gx
sw = A * gw
W = np.vstack([window(i, sx) for i in range(K)])


def corr_scalar(i, j, x):
    return float(np.sum(sw * W[i] * window(j, sx + x)))


# visible prime powers: support of pairTest is |x| < 4 => log n < 4
PP = []
for n in range(2, 54):
    for p in range(2, n + 1):
        if n % p == 0 and all(n % q for q in range(2, p)):
            m2, k = n, 0
            while m2 % p == 0:
                m2 //= p
                k += 1
            if m2 == 1:
                PP.append((n, float(np.log(p)), np.log(n)))
                break
PP.sort()
print(f"visible prime powers ({len(PP)}):", [n for n, _, _ in PP])

# --- arch quadrature on (0,4) ---
NARC = 16
NGL = 40
ax_gx, ax_gw = leggauss(NGL)
ys, ws = [], []
for b0 in range(NARC):
    lo, hi = 4.0 * b0 / NARC, 4.0 * (b0 + 1) / NARC
    ys.append(lo + (hi - lo) * (ax_gx + 1) / 2)
    ws.append((hi - lo) / 2 * ax_gw)
ys = np.concatenate(ys)
ws = np.concatenate(ws)

# precompute C_ij at the arch nodes and at +-log n
C_p = np.empty((K, K, len(ys)))
C_m = np.empty((K, K, len(ys)))
for i in range(K):
    for j in range(K):
        C_p[i, j] = [corr_scalar(i, j, y) for y in ys]
        C_m[i, j] = [corr_scalar(i, j, -y) for y in ys]
C_log_p = np.empty((K, K, len(PP)))
C_log_m = np.empty((K, K, len(PP)))
for i in range(K):
    for j in range(K):
        for t, (_, _, ln) in enumerate(PP):
            C_log_p[i, j, t] = corr_scalar(i, j, ln)
            C_log_m[i, j, t] = corr_scalar(i, j, -ln)
C0 = np.empty((K, K))
for i in range(K):
    for j in range(K):
        C0[i, j] = corr_scalar(i, j, 0.0)

ARCH = np.empty((K, K))
for i in range(K):
    for j in range(K):
        central = float(np.sum(ws * ((np.exp(ys / 2) * (C_p[i, j] + C_m[i, j])
                                      - 2 * C0[i, j]) / (2 * np.sinh(ys)))))
        ARCH[i, j] = (LOG4PI_GAMMA * C0[i, j] + central
                      + C0[i, j] * float(np.log(np.tanh(2.0))))

PRIME = np.zeros((K, K))
for t, (n, lam, _) in enumerate(PP):
    PRIME += (lam / np.sqrt(n)) * (C_log_p[:, :, t] + C_log_m[:, :, t])

M_TRUE = ARCH + PRIME

# --- committed 1112 bundle ---
_cert = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                     "1112_cert.json")
d = json.load(open(_cert))
cls = d["classes"][0]


def rat_matrix(rows):
    return np.array([[float(Fraction(v)) for v in row] for row in rows])


M_LO = rat_matrix(cls["M_lo"])
M_HI = rat_matrix(cls["M_hi"])
M_MID = rat_matrix(cls["M_mid"])

print()
print("=== (1) same-parity entries: M_true vs committed 1112 M_mid ===")
diffs_same = [abs(M_TRUE[i, j] - M_MID[i, j])
              for i in range(K) for j in range(K)
              if (i + j) % 2 == 0]
print(f"max |M_true - M_mid| over {len(diffs_same)} same-parity entries: "
      f"{max(diffs_same):.3e}   (expect ~1e-12: both-sides = 2*single)")

print()
print("=== (2) mixed-parity entries: predicted EXACT 0 (D1 parity) ===")
worst_mix = 0.0
for i in range(K):
    for j in range(K):
        if (i + j) % 2 == 1:
            worst_mix = max(worst_mix, abs(M_TRUE[i, j]))
            if M_LO[i, j] > 0 or M_HI[i, j] < 0:
                print(f"  BOX VIOLATION at ({i},{j}): M_true = "
                      f"{M_TRUE[i, j]:+.3e}, committed box = "
                      f"[{M_LO[i, j]:+.6f}, {M_HI[i, j]:+.6f}]")
print(f"max |M_true| over mixed entries: {worst_mix:.3e}   "
      f"(1112 committed has up to +-0.35 there)")

# --- (3) whitened top of M_true on V = ker R ---
print()
print("=== (3) Gram-whitened top on V = ker R, VANISH_S = (0, 0.5, 1) ===")
VANISH_S = (0.0, 0.5, 1.0)
R = np.empty((3, K))
for si, s in enumerate(VANISH_S):
    for j in range(K):
        R[si, j] = float(np.sum(sw * W[j] * np.exp(s * sx)))
G = C0.copy()
u, sv, vh = np.linalg.svd(R, full_matrices=True)
rank_r = int(np.sum(sv > 1e-11 * max(sv[0], 1.0)))
Zn = vh[rank_r:].T
print(f"rank(R) = {rank_r}, dim V = {Zn.shape[1]}")


def whitened_top(M):
    Pz = Zn.T @ G @ Zn
    L = np.linalg.cholesky((Pz + Pz.T) / 2.0)
    Li = np.linalg.inv(L)
    H = Li @ Zn.T @ M @ Zn @ Li.T
    ev = np.linalg.eigvalsh((H + H.T) / 2.0)
    return ev[-1], ev


top_true, spec_true = whitened_top(M_TRUE)
top_mid, _ = whitened_top(M_MID)
print(f"top(M_true |V whitened)   = {top_true:+.6e}")
print(f"spectrum: {['%.4e' % v for v in spec_true[::-1]]}")
print(f"top(committed M_mid |V)   = {top_mid:+.6e}   "
      f"(cert top_mid = {cls['top_mid']:+.6e}, U = {cls['U']:+.6e})")
print()
if top_true < 0:
    print(f"VERDICT: the TRUE gateMatrix is negative on ker R with margin "
          f"{-top_true:.3e}.  The 1112 margin architecture SURVIVES on the "
          f"true matrix; the chain repair reduces to D1 (parity zeros) + "
          f"D5 (box regeneration) with NO pole brick needed for D3.")
else:
    print("VERDICT: the TRUE gateMatrix is NOT negative on ker R.  The "
          "margin architecture does not transfer; D3 needs the "
          "preregistered pole-side restatement.")
