"""1109 - certified-optimal U by bisection on the 1108 interval machine.

Pre-registration: 1109_certified_optimal_U_preregistration.md
(committed before this run).  Byte-copy of the 1108 probe at
4d955f2 through the G-margin gate; the single certificate section
becomes a monotone oracle cert_of(U) - interval Cholesky of
T_int(U, NU*), NU* fixed (exact S-lemma duality made NU independent
of U) - bisected 40 steps on [f(NU*) - 5e-8, -4.0e-07], anchored by
G-anchor1108 (bit-stable reproduction of the 1108 certificate) and
G-bracket (registered fail side must fail).  Window class only;
the Lean gate Prop is NOT discharged; RH is not claimed.
"""
import importlib.util
import math
import os
import sys

import numpy as np
import mpmath as mp
from numpy.polynomial.legendre import leggauss
from scipy.linalg import cholesky, eigh
from scipy.optimize import minimize

HERE = os.path.dirname(os.path.abspath(__file__))
MOD_1101 = os.path.join(HERE, "1101_law34_interval_certifier_probe.py")

# G-env: importing the committed 1101 module runs its top-level flint
# check (ABORTs if python-flint arb is unusable) and hands us IV +
# C_ARCH VERBATIM - zero transcription.
_spec = importlib.util.spec_from_file_location("m1101", MOD_1101)
assert _spec is not None and _spec.loader is not None
m1101 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(m1101)
IV = m1101.IV
C_ARCH = m1101.C_ARCH

import flint as _flint
_flint.ctx.prec = 300

A_R = 2.0
K = 8
N_GL = 256
U_CERT = -4.0e-07
MARGIN_FLOAT = -4.5e-07
WIDTH_BUDGET = 2e-8
PIVOT_FLOOR = 1e-9
TAU = 1e-14                    # registered GL-rule truncation (prereg s2)
VANISH_S = (0.0, 0.5, 1.0)
F0_ANCHOR = -9.773e-07          # record 1107 f0 null-basis top(M)
U_HEADLINE = -1.40e-06          # registered pass bar (1109 s1)
BRACKET_MAX = 1e-13             # final HI-LO budget (1109 s1)
LAMZ60 = 1.443313051e-06        # diagnostic constant (1109 s1)


def abort(msg):
    print(f"VERDICT: ABORT-{msg}")
    sys.exit(0)


# ------------------------------------------------- phi (closed-form, arb)
from numpy.polynomial.legendre import leg2poly
LEG = [leg2poly(np.eye(K)[k]) for k in range(K)]   # power coeffs of P_k


def phi_iv(u_iv, k):
    """phi_k(u) = P_{k-1}(u/a) * exp(-1/(1-(u/a)^2)) or 0 outside."""
    x = u_iv * IV(1.0 / A_R)
    if x.absmax() >= 1.0:
        return IV(0)
    p = IV(LEG[k][-1])                      # Horner from the top degree
    for c in LEG[k][-2::-1]:
        p = p * x + IV(c)
    return p * (IV(-1) / (IV(1) - x * x)).exp()


# ------------------------------------------------------------ GL tables
xn, wn = leggauss(N_GL)
T_NODES = A_R * xn
T_WTS = A_R * wn
YN = (xn + 1.0) * A_R           # nodes on [0, 2a]
YW = wn * A_R                   # weights on [0, 2a]


def t_table(shift):
    """B_ij(shift) = int phi_i(t) phi_j(t - shift) dt (GL-256, arb).
    B(shift=0) is symmetric; general shift is NOT, no shortcut."""
    sh = shift if isinstance(shift, IV) else IV(shift)
    pt = [[phi_iv(IV(t), i) for i in range(K)] for t in T_NODES]
    ps = [[phi_iv(IV(t) - sh, j) for j in range(K)] for t in T_NODES]
    out = np.empty((K, K), dtype=object)
    for i in range(K):
        for j in range(K):
            acc = IV(0)
            for m in range(N_GL):
                acc = acc + IV(T_WTS[m]) * pt[m][i] * ps[m][j]
            out[i, j] = acc
    return out


def prime_powers():
    bound = int(math.floor(math.exp(2 * A_R)))
    out = []
    for p in range(2, bound + 1):
        if p > 1 and all(p % d for d in range(2, int(p ** 0.5) + 1)):
            pw = p
            while pw <= bound:
                if math.log(pw) < 2 * A_R - 1e-9:
                    out.append(pw)
                pw *= p
    return sorted(set(out))


PRIMES = prime_powers()

# ============================================== G-coef (class calibration)
mp.mp.dps = 40


def cheb_coeff_bump_poly(deg_hi, deg2, l):
    """a_l = (2/pi) int_0^pi bump(cos th) P_hi(cos th) P_d2(cos th) cos(l th)."""
    def f(th):
        c = mp.cos(th)
        s2 = mp.sin(th) ** 2
        if s2 == 0:
            return mp.mpf(0)
        return mp.exp(-1 / s2) * mp.legendre(deg_hi, c) * mp.legendre(deg2, c) \
            * mp.cos(l * th)
    edges = [mp.mpf(i) * mp.pi / (4 * l) for i in range(4 * l + 1)]
    return (mp.mpf(2) / mp.pi) * mp.quad(f, edges)


def run_g_coef():
    worst = 0.0
    for (dh, d2) in [(7, 7), (5, 7)]:
        for l in (100, 200, 300):
            a_l = abs(cheb_coeff_bump_poly(dh, d2, l))
            ratio = float(a_l) * math.exp(2 * math.sqrt(l))
            worst = max(worst, ratio)
            print(f"  G-coef g=bump*P{dh}*P{d2} l={l}: |a_l|={float(a_l):.2e} "
                  f"ratio={ratio:.2e}")
    return worst


print("G-coef calibration (mpmath dps=40)...")
gcoef = run_g_coef()
print(f"G-coef worst ratio = {gcoef:.2e} (assert <= 10)")
if gcoef > 10.0:
    abort("COEF")

# --------------------------------------------------- build all interval data
print(f"building tables: {len(YN)} y-nodes + {len(PRIMES)} prime shifts "
      f"+ G + R (GL-256 nested, arb 300-bit)...")
Y_TAB = np.empty((len(YN), K, K), dtype=object)
for ky, y in enumerate(YN):
    Y_TAB[ky] = t_table(IV(y))
    if (ky + 1) % 32 == 0:
        print(f"  y-nodes {ky + 1}/{len(YN)}")

G_TAB = t_table(IV(0.0))

R_MAT = np.empty((3, K), dtype=object)
for si, s in enumerate(VANISH_S):
    for j in range(K):
        acc = IV(0)
        for m in range(N_GL):
            t_iv = IV(T_NODES[m])
            e_st = IV(1) if s == 0.0 else IV((t_iv * IV(s)).iv.exp())
            acc = acc + IV(T_WTS[m]) * phi_iv(t_iv, j) * e_st
        R_MAT[si, j] = acc

P_MAT = np.empty((K, K), dtype=object)
for i in range(K):
    for j in range(K):
        P_MAT[i, j] = IV(0)
def von_mangoldt_log(q):
    """Lambda(q) = log p for q = p^k (f0.lam_sieve convention - the
    base-prime log, NOT log q: fix batch 2, run-1 diag)."""
    for p in range(2, q + 1):
        k = 0
        pw = q
        while pw % p == 0 and pw > 1:
            pw //= p
            k += 1
        if pw == 1 and k >= 1:
            return math.log(p)
    raise AssertionError(q)


for n_q, q in enumerate(PRIMES):
    xi = IV(IV(q).iv.log())                 # shift position: log q
    w = IV(von_mangoldt_log(q)) / IV(IV(q).iv.sqrt())   # weight: log p / sqrt q
    tab = t_table(-xi)             # phi_j(t + xi)
    for i in range(K):
        for j in range(K):
            P_MAT[i, j] = P_MAT[i, j] + (IV(2) * w) * tab[i, j]
    print(f"  prime {n_q + 1}/{len(PRIMES)}: q={q}")

J_MAT = np.empty((K, K), dtype=object)
for i in range(K):
    for j in range(K):
        J_MAT[i, j] = IV(0)
for ky, y in enumerate(YN):
    y_iv = IV(y)
    e_y2 = IV((y_iv * IV(0.5)).iv.exp())
    den = IV(2) * IV(y_iv.iv.sinh())
    S = Y_TAB[ky] + np.swapaxes(Y_TAB[ky], 0, 1)   # symmetric in (i,j)
    for i in range(K):
        for j in range(K):
            J_MAT[i, j] = J_MAT[i, j] + IV(YW[ky]) * (
                e_y2 * S[i, j] - IV(2) * G_TAB[i, j]) / den
TAIL = IV(IV(A_R).iv.tanh()).log()                  # log tanh(a)
A_MAT = np.empty((K, K), dtype=object)
for i in range(K):
    for j in range(K):
        A_MAT[i, j] = (C_ARCH + TAIL) * G_TAB[i, j] + J_MAT[i, j]
M_MAT = np.empty((K, K), dtype=object)
for i in range(K):
    for j in range(K):
        M_MAT[i, j] = A_MAT[i, j] + P_MAT[i, j]

midf = lambda m: np.array([[float(e.iv.mid()) for e in row]
                           for row in np.atleast_2d(m)], dtype=float)


def maxw(m):
    return max(e.width() for e in np.ravel(m))


G = midf(G_TAB)
R = midf(R_MAT)
A = midf(A_MAT)
P = midf(P_MAT)
M = midf(M_MAT)

# ---------------------------------------------------------- G-width gate
w_max = max(maxw(G_TAB), maxw(R_MAT), maxw(A_MAT), maxw(P_MAT), maxw(M_MAT))
print(f"max entry interval width = {w_max:.2e} (budget {WIDTH_BUDGET:.0e})")
if w_max > WIDTH_BUDGET:
    abort("BUDGET")

# --------------------------------------------------- G-agree diagnostic
# top of the pencil RESTRICTED to the float null space of R (same
# rank rule as f0.null_setup), then compared to the f0 anchor; the
# unconstrained raw pencil would legitimately sit at O(10).
_, svr, vhr = np.linalg.svd(R, full_matrices=True)
rank_r = int(np.sum(svr > 1e-11 * max(svr[0], 1.0)))
Zn = vhr[rank_r:].T                          # 8 x (8-rank) null basis
Bz = Zn.T @ G @ Zn
Mz = Zn.T @ M @ Zn
Lz = cholesky(Bz, lower=True)
Lzi = np.linalg.inv(Lz)
Bpen = Lzi @ Mz @ Lzi.T
top_mid = float(eigh((Bpen + Bpen.T) / 2.0, eigvals_only=True)[-1])
print(f"midpoint constrained top = {top_mid:+.6e} "
      f"(f0 anchor {F0_ANCHOR:+.3e}; diff {top_mid - F0_ANCHOR:.2e})")
if abs(top_mid - F0_ANCHOR) > 1e-2:
    abort("AGREE")

# full-space pencil for the S-lemma dual f(NU)
Lg = cholesky(G, lower=True)
Lgi = np.linalg.inv(Lg)

# --------------------------------------------------- S-lemma candidate NU
def f_grad(nu_flat):
    nu = nu_flat.reshape(3, K)
    Mp = M + R.T @ nu + nu.T @ R
    Bc = Lgi @ Mp @ Lgi.T
    ev, evec = eigh((Bc + Bc.T) / 2.0)
    lam = float(ev[-1])
    ytil = Lgi.T @ evec[:, -1]
    g = np.stack([2.0 * (R[si] @ ytil) * ytil for si in range(3)])
    return lam, g.ravel()


def f_only(nu_flat):
    return f_grad(nu_flat)[0]


def bfgs_from(nu0):
    r = minimize(f_grad, nu0.ravel(), jac=True, method="L-BFGS-B",
                 options={"maxiter": 4000, "ftol": 1e-18, "gtol": 1e-15})
    return f_only(r.x), r.x.reshape(3, K)


# warm start from the KKT stationarity of the top pencil pair:
# (R^T nu + nu^T R) c* = (lam0 G - M) c*,  linear in nu entries:
#   col (s,t): term1 vector R[s]*c_star[t], term2 adds rc[s] at row t.
# c* here is the RAW (8-dim, G-normalized) constrained top vector.
Bpen_s = (Bpen + Bpen.T) / 2.0
ev0, ec0 = eigh(Bpen_s)
u_top = ec0[:, -1]
lam0 = float(ev0[-1])
c_star = Zn @ (Lzi.T @ u_top)                # reduced -> raw coordinates
rhs = lam0 * G @ c_star - M @ c_star
A_ls = np.zeros((K, 3 * K))
rc = R @ c_star
for si in range(3):
    for t in range(K):
        A_ls[:, si * K + t] = R[si] * c_star[t]
        A_ls[t, si * K + t] += rc[si]
nu_warm, *_ = np.linalg.lstsq(A_ls, rhs, rcond=None)

starts = [np.zeros((3, K)), nu_warm.reshape(3, K)]
rng = np.random.default_rng(1108)
for _ in range(3):
    starts.append(nu_warm.reshape(3, K) + 1e-2 * rng.standard_normal((3, K)))
best = min((bfgs_from(s) for s in starts), key=lambda x: x[0])
f_star, NU = best
print(f"BFGS: f(NU*) = {f_star:+.6e}  (G-margin gate: <= {MARGIN_FLOAT:.1e})")
if f_star > MARGIN_FLOAT:
    print("no candidate clears the registered margin")
    print("VERDICT: STRADDLE-OPEN")
    print("DONE")
    sys.exit(0)

# ------------------------- interval Cholesky oracle, monotone in U (1109)
def T_int_of(U_val):
    T = np.empty((K, K), dtype=object)
    for i in range(K):
        for j in range(K):
            add = IV(0)
            for si in range(3):
                nu_iv = IV(float(NU[si, i]))
                add = add + nu_iv * R_MAT[si, j] + R_MAT[si, i] * IV(float(NU[si, j]))
            e = IV(U_val) * G_TAB[i, j] - M_MAT[i, j] - add
            # widen by the registered truncation TAU (4x): the arb widths
            # carry ROUNDING only; rule-vs-integral truncation enters here
            m = float(e.iv.mid())
            r = float(e.iv.rad()) + 4.0 * TAU
            T[i, j] = IV.span(m - r, m + r)
    return T


# FIX BATCH 1 (run-1 ABORT-BRACKET): the 1108 pivot test used
# p.absmin() >= floor, which is SIGN-BLIND - a strictly negative
# pivot interval has absmin = its endpoint nearest zero and PASSES.
# PSD requires every pivot proved POSITIVE: test the LOWER endpoint
# lo = mid - width/2 >= floor.  Run-1's G-bracket PASS at a U below
# the top (where the exact T has a provably negative direction,
# c*'Tc* = U - top = -5e-08) caught exactly this hole.
def piv_lows(U_val):
    """list of pivot LOWER endpoints of the interval Cholesky walk
    (diagnostic + gate feed)."""
    cur = [[e for e in row] for row in T_int_of(U_val)]
    lows = []
    for k in range(K):
        p = cur[k][k]
        lows.append(p.midf() - p.width() / 2.0)
        for i in range(k + 1, K):
            for j in range(k + 1, K):
                cur[i][j] = cur[i][j] - cur[i][k] * cur[k][j] / p
    return lows


def cert_of(U_val):
    """(pass, min pivot lower endpoint) - fix batch 1 predicate."""
    lows = piv_lows(U_val)
    return min(lows) >= PIVOT_FLOOR, min(lows)


def t_float_eigmin(U_val):
    """float64 smallest eigenvalue of the midpoint T(NU*, U): shows
    which side of zero the dangerous direction sits on."""
    Tf = U_val * G - M - R.T @ NU - NU.T @ R
    return float(eigh((Tf + Tf.T) / 2.0, eigvals_only=True)[0])


# G-anchor1108: deterministic NU* must reproduce the registered cert.
ok_a, piv_a = cert_of(U_CERT)
print(f"G-anchor1108: U={U_CERT:.1e} -> "
      f"{'PASS' if ok_a else 'FAIL'} (min pivot LOW {piv_a:.2e})")
print(f"  float eigmin(T(anchor)) = {t_float_eigmin(U_CERT):+.3e}")
print(f"  anchor pivot lows: {['%.3e' % x for x in piv_lows(U_CERT)]}")
if not ok_a:
    abort("ANCHOR")

# G-bracket: the registered fail side must fail (floor slope check).
U_LO = f_star - 5.0e-8
ok_l, piv_l = cert_of(U_LO)
print(f"G-bracket: U={U_LO:.6e} -> "
      f"{'PASS' if ok_l else 'FAIL'} (min pivot LOW {piv_l:.2e})")
print(f"  float eigmin(T(bracket)) = {t_float_eigmin(U_LO):+.3e}")
print(f"  bracket pivot lows: {['%.3e' % x for x in piv_lows(U_LO)]}")
if ok_l:
    abort("BRACKET")

U_HI = U_CERT
for it in range(40):
    U_MID = 0.5 * (U_LO + U_HI)
    if U_MID == U_LO or U_MID == U_HI:
        print(f"bisection float-exhausted after {it + 1} steps")
        break
    ok_m, _ = cert_of(U_MID)
    if ok_m:
        U_HI = U_MID
    else:
        U_LO = U_MID
bracket = U_HI - U_LO
ok_h, piv_h = cert_of(U_HI)          # re-certify the final HI end
if not ok_h:
    abort("RECERT")
print(f"certified-optimal U_opt = {U_HI:+.9e} (bracket {bracket:.1e}, "
      f"min pivot LOW {piv_h:.2e})")
print(f"1108 bound was {U_CERT:.1e}; bound lowered by {U_CERT - U_HI:.3e}")
print(f"diagnostic U_opt + LAMZ60 ({LAMZ60:.9e}) = {U_HI + LAMZ60:+.3e}")
if bracket > BRACKET_MAX:
    abort("BRACKETW")
if U_HI <= U_HEADLINE:
    print(f"CERTIFIED: top(A+P)|_V <= {U_HI:+.9e} "
          f"(headline bar {U_HEADLINE:.1e} met)")
    print("VERDICT: PASS-ENCLOSED")
else:
    print(f"certified bound {U_HI:+.9e} misses the registered headline "
          f"bar {U_HEADLINE:.1e}; prediction falsified, bound stands")
    print("VERDICT: STRADDLE-TIGHT")
print("DONE")
