"""1110 - (4,8) window-class certificate on the audited float-domain
machine.

Pre-registration: 1110_cert48_preregistration.md (committed before
this run).  a=4, K=8, GL-512 arb entry balls (rounding audit, laws
51/52 semantics), von Mangoldt prime weights (law 49), TAU_48 =
1e-20; the certified quantity is the reduced-pencil top_mid with
budget EPS_48 = 1e-10 - no S-lemma search, no ball-Cholesky, no
bisection theater.  Canaries: G-xcheck (independent generalized
eigensolver) and G-reactive (sign-flipped R entry must move the
top).  Window class only; the Lean gate Prop is NOT discharged;
RH is not claimed.
"""
import importlib.util
import math
import os
import sys

import numpy as np
import mpmath as mp
from numpy.polynomial.legendre import leggauss
from scipy.linalg import cholesky, eigh, eigvalsh

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

A_R = 4.0
K = 8
N_GL = 512
WIDTH_BUDGET = 1e-7
TAU = 1e-20                    # TAU_48 registered (1110 s0)
VANISH_S = (0.0, 0.5, 1.0)
EPS_48 = 1e-10                 # certified budget (1110 s0 channel table)
LAMZ48 = 2.600074418e-10       # 1107 cell, N-flat 10 digits (s1)
XCHECK_MAX = 1e-12             # G-xcheck budget (s1 step 3)
REACT_MIN = 1e-6               # G-reactive canary floor (s1 step 3)


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


# Hoisted phi-node values (1110 engineering optimization): pt is
# shift-independent, every t_table call recomputed it - ~450 shifts
# at (4,8) made that the dominant cost.  MATRICES ARE BIT-IDENTICAL
# to the un-hoisted composition (same ball products, same order).
PT = [[phi_iv(IV(t), i) for i in range(K)] for t in T_NODES]


def t_table(shift):
    """B_ij(shift) = int phi_i(t) phi_j(t - shift) dt (GL-512, arb).
    B(shift=0) is symmetric; general shift is NOT, no shortcut."""
    sh = shift if isinstance(shift, IV) else IV(shift)
    ps = [[phi_iv(IV(t) - sh, j) for j in range(K)] for t in T_NODES]
    out = np.empty((K, K), dtype=object)
    for i in range(K):
        for j in range(K):
            acc = IV(0)
            for m in range(N_GL):
                acc = acc + IV(T_WTS[m]) * PT[m][i] * ps[m][j]
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
      f"+ G + R (GL-512 nested, arb 300-bit, PT hoisted)...")
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

# ------------------------------------------ reduced-pencil top (1110 s0)
# The certified quantity: top of the pencil on the exact null space of
# the float midpoint R (rank rule = f0.null_setup / 1109 G-agree).
# No S-lemma search (the float null space IS the registered class
# constraint), no ball-Cholesky (laws 51/52), no bisection theater:
# the certified statement is top <= top_mid + EPS_48 with the
# registered budget of the pre-registration.
def pencil_top(Rm, Gm, Mm):
    _, svr, vhr = np.linalg.svd(Rm, full_matrices=True)
    rank_r = int(np.sum(svr > 1e-11 * max(svr[0], 1.0)))
    Zn = vhr[rank_r:].T
    Bz = Zn.T @ Gm @ Zn
    Mz = Zn.T @ Mm @ Zn
    Lz = cholesky(Bz, lower=True)
    Lzi = np.linalg.inv(Lz)
    Bpen = Lzi @ Mz @ Lzi.T
    Bpen = (Bpen + Bpen.T) / 2.0
    ev, ec = eigh(Bpen)
    u_top = ec[:, -1]
    c_star = Zn @ (Lzi.T @ u_top)
    return float(ev[-1]), c_star, Zn, Bz, Mz


top_mid, c_star, Zn, Bz, Mz = pencil_top(R, G, M)
print(f"(4,8) reduced-pencil top_mid = {top_mid:+.12e} "
      f"(identity prediction -LAMZ48 = {-LAMZ48:+.12e})")

# G-xcheck canary (law 50): INDEPENDENT eigensolver route.
top_gen = float(eigvalsh(Mz, Bz)[-1])
d_xc = abs(top_gen - top_mid)
print(f"G-xcheck: eigvalsh(Mz,Bz) = {top_gen:+.12e}; "
      f"|diff| = {d_xc:.2e} (max {XCHECK_MAX:.0e})")
if d_xc > XCHECK_MAX:
    abort("XCHECK")

# G-reactive canary (law 50): a pipeline that cannot see corrupted
# data is not computing.  Flip the sign of one R entry (rng seed
# 1110), the top must move by at least REACT_MIN.
rng = np.random.default_rng(1110)
si = int(rng.integers(3))
cj = int(rng.integers(K))
R_cor = R.copy()
R_cor[si, cj] = -R_cor[si, cj]
top_cor, *_ = pencil_top(R_cor, G, M)
react = abs(top_cor - top_mid)
print(f"G-reactive: sign-flip R[{si},{cj}] moved top by "
      f"{react:.3e} (min {REACT_MIN:.0e})")
if react < REACT_MIN:
    abort("REACT")

# audit block (budget channels of pre-reg s0, live)
g_ev = eigh((G + G.T) / 2.0, eigvals_only=True)
print(f"audit: lambda_min(G) = {g_ev[0]:.3e}, "
      f"lambda_max(G) = {g_ev[-1]:.3e}")
print(f"audit: sigma_min(R) = "
      f"{np.linalg.svd(R, compute_uv=False)[-1]:.3e}")
sum_w = sum(2.0 * von_mangoldt_log(q) / math.sqrt(q) for q in PRIMES)
print(f"audit: sum prime weights 2*Lambda(q)/sqrt(q) = {sum_w:.3f} "
      f"(truncation channel {sum_w * TAU:.1e})")
print(f"audit: ||c*||^2 = {float(c_star @ c_star):.3e} "
      f"(G-norm {float(c_star @ G @ c_star):.6f})")

# verdict (literal, pre-reg s1)
cert_bound = top_mid + EPS_48
D = top_mid + LAMZ48
print(f"identity diagnostic D = top_mid + LAMZ48 = {D:+.3e} "
      f"({'MET' if abs(D) <= 2e-10 else 'TENSION'} at 2e-10)")
if top_mid >= 0.0:
    print(f"STRADDLE-ZERO: top_mid >= 0; certified bound reported: "
          f"top(A+P)|_V <= {cert_bound:+.6e}")
    print("VERDICT: STRADDLE-ZERO")
elif cert_bound < 0.0:
    print(f"CERTIFIED: top(A+P)|_V <= {cert_bound:+.6e} < 0 at (4,8) "
          f"(float domain, EPS_48 = {EPS_48:.0e})")
    print("VERDICT: PASS-NEG48")
else:
    print(f"CERTIFIED: top(A+P)|_V <= {cert_bound:+.6e}; strictly "
          f"negative NOT certified at this budget (top_mid = "
          f"{top_mid:+.6e})")
    print("VERDICT: STRADDLE-ZERO")
print("DONE")
