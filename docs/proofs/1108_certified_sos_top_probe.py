"""1108 - interval-certified upper bound on the (2,8) window gate top.

Pre-registration: 1108_certified_sos_top_preregistration.md (committed
before this run).  Claims top(A+P)|_V <= U = -4.0e-07 via an S-lemma
multiplier certificate (T(NU) := U*G - M - R^T NU - NU^T R PSD, NU in
R^{3x8}) verified by interval Cholesky on arb interval entries of
A, P, G, R (GL-256 rules, registered truncation TAU = 1e-14, G-coef
Gevrey-class calibration).  Window class only; the Lean gate Prop is
NOT discharged; RH is not claimed.
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
for n_q, q in enumerate(PRIMES):
    xi = IV(IV(q).iv.log())
    w = xi / IV(IV(q).iv.sqrt())            # arb log/sqrt (f0 float agrees
                                            # to ~1e-16, below TAU)
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
Lg = cholesky(G, lower=True)
Lgi = np.linalg.inv(Lg)
Bpen = Lgi @ M @ Lgi.T
top_mid = float(eigh((Bpen + Bpen.T) / 2.0, eigvals_only=True)[-1])
print(f"raw-basis midpoint constrained top = {top_mid:+.6e} "
      f"(f0 anchor {F0_ANCHOR:+.3e}; diff {top_mid - F0_ANCHOR:.2e})")
if abs(top_mid - F0_ANCHOR) > 1e-2:
    abort("AGREE")

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
Bpen_s = (Bpen + Bpen.T) / 2.0
ev0, ec0 = eigh(Bpen_s)
u_top = ec0[:, -1]
lam0 = float(ev0[-1])
c_star = Lgi.T @ u_top                       # G-normalized raw vector
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

# ------------------------------------------ interval Cholesky of T_int(NU)
T_INT = np.empty((K, K), dtype=object)
for i in range(K):
    for j in range(K):
        add = IV(0)
        for si in range(3):
            nu_iv = IV(float(NU[si, i]))
            add = add + nu_iv * R_MAT[si, j] + R_MAT[si, i] * IV(float(NU[si, j]))
        e = IV(U_CERT) * G_TAB[i, j] - M_MAT[i, j] - add
        # widen by the registered truncation TAU (4x): the arb widths
        # carry ROUNDING only; rule-vs-integral truncation enters here
        m = float(e.iv.mid())
        r = float(e.iv.rad()) + 4.0 * TAU
        T_INT[i, j] = IV.span(m - r, m + r)

cur = [[T_INT[i, j] for j in range(K)] for i in range(K)]
piv_min = np.inf
ok = True
for k in range(K):
    p = cur[k][k]
    if p.absmin() < PIVOT_FLOOR:
        print(f"pivot {k}: absmin {p.absmin():.2e} < {PIVOT_FLOOR:.0e} FAIL")
        ok = False
        break
    piv_min = min(piv_min, p.absmin())
    for i in range(k + 1, K):
        for j in range(k + 1, K):
            cur[i][j] = cur[i][j] - cur[i][k] * cur[k][j] / p
if ok:
    print(f"interval Cholesky PASS (min pivot absmin {piv_min:.2e})")
    print(f"CERTIFIED: top(A+P)|_V <= {U_CERT:.1e} on the window class")
    print("VERDICT: PASS")
else:
    print(f"best f(NU*) = {f_star:+.3e}; widths {w_max:.1e}")
    print("VERDICT: STRADDLE-OPEN")
print("DONE")
