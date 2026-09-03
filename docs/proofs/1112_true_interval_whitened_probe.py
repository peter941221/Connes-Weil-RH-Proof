"""1112 - true-interval (dependency-safe) PSD certificate of the reduced
pencil, both classes.

Pre-registration: 1112_true_interval_whitened_preregistration.md
(committed before this run).  The positive test is ENTRYWISE diagonal
dominance after TWO FIXED-float congruences (Gram whitening L, then
slack whitening Rc of the float midpoint): uncertain data reaches the
test only through affine maps, so no ball/interval Cholesky ever touches
an uncertain pivot (laws 51/52 compliance).  Boxes = arb radius +
8-ulp float-representation widening + registered GL-truncation channel
(20 + 10*sum_w) * TAU.  Output per class: PASS-IV / STRADDLE-IV with
the full slack profile, plus docs/proofs/1112_cert.json - outward
rational enclosures + the fixed float data as the ingestion bundle for
the 1111 Lean bridge's future rational-Cholesky consumer.
Window classes only; the Lean gate Prop is NOT discharged; RH is not
claimed.
"""
import importlib.util
import json
import math
import os
import sys
from fractions import Fraction

from typing import NoReturn

import numpy as np
import mpmath as mp
from numpy.polynomial.legendre import leggauss, leg2poly
from scipy.linalg import cholesky, LinAlgError, eigh, eigvalsh

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

K = 8
VANISH_S = (0.0, 0.5, 1.0)
WIDTH_BUDGET = 1e-7
WIDEN_ULPS = 8                       # 1112 s0 step 1
XCHECK_MAX = 1e-12                   # law 50/53 symmetrized xcheck (1110)
REACT_MIN = 1e-6                     # law 54 load-bearing-row leverage
LEG = [leg2poly(np.eye(K)[k]) for k in range(K)]

# class, N_GL, TAU, DELTA (all registered in 1112 s0/s1)
CLASSES = [
    dict(tag="28", A_R=2.0, N_GL=256, TAU=1e-14, DELTA=4.0e-07, EPS=1e-09),
    dict(tag="48", A_R=4.0, N_GL=512, TAU=1e-20, DELTA=1.0e-10, EPS=1e-10),
]


def abort(msg) -> "NoReturn":
    print(f"VERDICT: ABORT-{msg}")
    sys.exit(0)


# ------------------------------------------------- phi (closed-form, arb)
def phi_iv(u_iv, k, A_R):
    """phi_k(u) = P_{k-1}(u/a) * exp(-1/(1-(u/a)^2)) or 0 outside."""
    x = u_iv * IV(1.0 / A_R)
    if x.absmax() >= 1.0:
        return IV(0)
    p = IV(LEG[k][-1])                      # Horner from the top degree
    for c in LEG[k][-2::-1]:
        p = p * x + IV(c)
    return p * (IV(-1) / (IV(1) - x * x)).exp()


def prime_powers(A_R):
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


def von_mangoldt_log(q):
    """Lambda(q) = log p for q = p^k (f0.lam_sieve convention, law 49)."""
    for p in range(2, q + 1):
        k = 0
        pw = q
        while pw % p == 0 and pw > 1:
            pw //= p
            k += 1
        if pw == 1 and k >= 1:
            return math.log(p)
    raise AssertionError(q)


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


print("G-coef calibration (mpmath dps=40, shared across classes)...")
worst = 0.0
for (dh, d2) in [(7, 7), (5, 7)]:
    for l in (100, 200, 300):
        a_l = abs(cheb_coeff_bump_poly(dh, d2, l))
        ratio = float(a_l) * math.exp(2 * math.sqrt(l))
        worst = max(worst, ratio)
print(f"G-coef worst ratio = {worst:.2e} (assert <= 10)")
if worst > 10.0:
    abort("COEF")


# ================================================ per-class interval build
def build_class(A_R, N_GL):
    """Returns arb matrices (G_TAB, R_MAT, M_MAT) via the 1108/1110 rules."""
    xn, wn = leggauss(N_GL)
    T_NODES = A_R * xn
    T_WTS = A_R * wn
    YN = (xn + 1.0) * A_R
    YW = wn * A_R
    PT = [[phi_iv(IV(t), i, A_R) for i in range(K)] for t in T_NODES]

    def t_table(shift):
        sh = shift if isinstance(shift, IV) else IV(shift)
        ps = [[phi_iv(IV(t) - sh, j, A_R) for j in range(K)] for t in T_NODES]
        out = np.empty((K, K), dtype=object)
        for i in range(K):
            for j in range(K):
                acc = IV(0)
                for m in range(N_GL):
                    acc = acc + IV(T_WTS[m]) * PT[m][i] * ps[m][j]
                out[i, j] = acc
        return out

    PRIMES = prime_powers(A_R)
    print(f"  [{A_R:.0f}] building: {len(YN)} y-nodes + {len(PRIMES)} shifts "
          f"(GL-{N_GL}, arb 300-bit, PT hoisted)...")
    Y_TAB = np.empty((len(YN), K, K), dtype=object)
    for ky, y in enumerate(YN):
        Y_TAB[ky] = t_table(IV(y))
        if (ky + 1) % 128 == 0:
            print(f"  [{A_R:.0f}] y-nodes {ky + 1}/{len(YN)}")

    G_TAB = t_table(IV(0.0))
    R_MAT = np.empty((3, K), dtype=object)
    for si, s in enumerate(VANISH_S):
        for j in range(K):
            acc = IV(0)
            for m in range(N_GL):
                t_iv = IV(T_NODES[m])
                e_st = IV(1) if s == 0.0 else IV((t_iv * IV(s)).iv.exp())
                acc = acc + IV(T_WTS[m]) * phi_iv(t_iv, j, A_R) * e_st
            R_MAT[si, j] = acc

    P_MAT = np.empty((K, K), dtype=object)
    for i in range(K):
        for j in range(K):
            P_MAT[i, j] = IV(0)
    for q in PRIMES:
        xi = IV(IV(q).iv.log())
        w = IV(von_mangoldt_log(q)) / IV(IV(q).iv.sqrt())
        tab = t_table(-xi)             # phi_j(t + xi)
        for i in range(K):
            for j in range(K):
                P_MAT[i, j] = P_MAT[i, j] + (IV(2) * w) * tab[i, j]

    J_MAT = np.empty((K, K), dtype=object)
    for i in range(K):
        for j in range(K):
            J_MAT[i, j] = IV(0)
    for ky, y in enumerate(YN):
        y_iv = IV(y)
        e_y2 = IV((y_iv * IV(0.5)).iv.exp())
        den = IV(2) * IV(y_iv.iv.sinh())
        S = Y_TAB[ky] + np.swapaxes(Y_TAB[ky], 0, 1)
        for i in range(K):
            for j in range(K):
                J_MAT[i, j] = J_MAT[i, j] + IV(YW[ky]) * (
                    e_y2 * S[i, j] - IV(2) * G_TAB[i, j]) / den
    TAIL = IV(IV(A_R).iv.tanh()).log()
    A_MAT = np.empty((K, K), dtype=object)
    for i in range(K):
        for j in range(K):
            A_MAT[i, j] = (C_ARCH + TAIL) * G_TAB[i, j] + J_MAT[i, j]
    M_MAT = np.empty((K, K), dtype=object)
    for i in range(K):
        for j in range(K):
            M_MAT[i, j] = A_MAT[i, j] + P_MAT[i, j]
    return G_TAB, R_MAT, M_MAT, PRIMES


def mid_of(m):
    return np.array([[float(e.iv.mid()) for e in row]
                     for row in np.atleast_2d(m)], dtype=float)


def rad_of(m):
    return np.array([[e.width() / 2.0 for e in row]
                     for row in np.atleast_2d(m)], dtype=float)


def maxw(m):
    return max(e.width() for e in np.ravel(m))


# ==================================================== certification (s0)
def certify(cl):
    A_R, N_GL, TAU, DELTA, EPS = (cl["A_R"], cl["N_GL"], cl["TAU"],
                                  cl["DELTA"], cl["EPS"])
    print(f"\n==== class ({A_R:.0f},8): GL-{N_GL}, TAU={TAU:.0e}, "
          f"DELTA={DELTA:.1e}, EPS={EPS:.0e} ====")
    G_TAB, R_MAT, M_MAT, PRIMES = build_class(A_R, N_GL)
    G, R, M = mid_of(G_TAB), mid_of(R_MAT), mid_of(M_MAT)
    wM = rad_of(M_MAT)
    w_max = max(maxw(G_TAB), maxw(R_MAT), maxw(M_MAT))
    print(f"max entry arb width = {w_max:.2e} (budget {WIDTH_BUDGET:.0e})")
    if w_max > WIDTH_BUDGET:
        abort("BUDGET")
    # registered box half-width (1112 s0 step 1): arb radius + ulp widen
    # + truncation channel, per entry, for M and G alike.
    sum_w2 = sum(2.0 * von_mangoldt_log(q) / math.sqrt(q) for q in PRIMES)
    TRUNC = (20.0 + 10.0 * sum_w2) * TAU
    print(f"box channels: arb rad (above), ulp widen x{WIDEN_ULPS}, "
          f"TRUNC = {TRUNC:.2e} (sum_w2 = {sum_w2:.1f})")

    # fixed float null basis + Gram whitening
    _, svr, vhr = np.linalg.svd(R, full_matrices=True)
    rank_r = int(np.sum(svr > 1e-11 * max(svr[0], 1.0)))
    Zn = vhr[rank_r:].T
    Pz = Zn.T @ G @ Zn
    try:
        L = cholesky((Pz + Pz.T) / 2.0, lower=True)
    except LinAlgError:
        abort("GRAMCHOL")
    C = np.linalg.inv(L) @ Zn.T                     # H = C M C^T
    n_dim = Zn.shape[1]

    # affine interval image of M; self-review rigor fixes (pre-commit):
    # (1) the SYMMETRIC pencil's entry radius is (w_ij + w_ji)/2 exactly -
    # symmetrize the box half-width BEFORE the congruence, never after; the
    # raw |CMC - CMC^T| is M's true skewness (one-directional prime shifts,
    # law 53 provenance), NOT a rounding term - it must not enter radii.
    # FIX BATCH 1 (channel audit, registered pre-rerun after the (4,8)
    # prediction falsified UPWARD; law-47 mirror - a PASS must survive
    # re-derivation of its own arithmetic): the float CENTER of each
    # affine image differs from the exact rational product (all fixed
    # float matrices are read as EXACT rationals in the soundness chain,
    # so the center displacement must enter the RADIUS as a bound, not a
    # floor). Channel: CENTER_CHOL := 4*eps * (|X| @ |mid| @ |Y|T), the
    # standard two-product matmul rounding bound (eps = float64 machine
    # epsilon; realized displacement observed 6.2e-11 at (4,8), far above
    # the deleted 1e-13 floor).
    CENTER_CHOL = 4.0 * np.finfo(float).eps
    wM_box = wM + WIDEN_ULPS * np.array(
        [[math.ulp(v) for v in row] for row in mid_of(M_MAT)]) + TRUNC
    wM_box = (wM_box + wM_box.T) / 2.0
    wG_box = rad_of(G_TAB) + WIDEN_ULPS * np.array(
        [[math.ulp(v) for v in row] for row in G]) + TRUNC
    wG_box = (wG_box + wG_box.T) / 2.0
    CMC = C @ M @ C.T
    CMC_sym = (CMC + CMC.T) / 2.0
    HRAD = np.abs(C) @ wM_box @ np.abs(C).T \
        + CENTER_CHOL * (np.abs(C) @ np.abs(M) @ np.abs(C).T)
    top_mid = float(eigvalsh(CMC_sym)[-1])
    print(f"reduced top_mid = {top_mid:+.12e}; lambda_min(Pz)="
          f"{eigh((Pz + Pz.T) / 2.0, eigvals_only=True)[0]:.3e}; "
          f"||L^-1||_2^2 = {1.0 / eigh((Pz + Pz.T) / 2.0, eigvals_only=True)[0]:.3e}")

    # G-xcheck canary (law 50/53): symmetrized generalized route
    Mz = Zn.T @ M @ Zn
    top_gen = float(eigvalsh((Mz + Mz.T) / 2.0, (Pz + Pz.T) / 2.0)[-1])
    d_xc = abs(top_gen - top_mid)
    print(f"G-xcheck |diff| = {d_xc:.2e} (max {XCHECK_MAX:.0e})")
    if d_xc > XCHECK_MAX:
        abort("XCHECK")

    # G-contain canary (1112 s1): Gershgorin bounds of the box must cover
    # the midpoint's own top.
    lo_d = np.diag(CMC_sym) - HRAD.diagonal()
    hi_off = np.abs(CMC_sym) + HRAD
    np.fill_diagonal(hi_off, 0.0)
    gg_hi = float(np.max(np.diag(CMC_sym) + HRAD.diagonal() + hi_off.sum(1)))
    if not (lo_d.min() <= top_mid <= gg_hi):
        print(f"containment violated: box gg-range [{lo_d.min():.2e}, "
              f"{gg_hi:.2e}] vs top {top_mid:.2e}")
        abort("CONTAIN")

    # G-reactive canary (law 54): load-bearing row offset must move top.
    R_cor = R.copy()
    R_cor[1, :] += 0.1
    _, svr2, vhr2 = np.linalg.svd(R_cor, full_matrices=True)
    rk2 = int(np.sum(svr2 > 1e-11 * max(svr2[0], 1.0)))
    Z2 = vhr2[rk2:].T
    P2 = Z2.T @ G @ Z2
    L2 = np.linalg.cholesky((P2 + P2.T) / 2.0)
    pen2 = np.linalg.inv(L2) @ Z2.T @ M @ Z2 @ np.linalg.inv(L2).T
    top_cor = float(eigvalsh((pen2 + pen2.T) / 2.0)[-1])
    react = abs(top_cor - top_mid)
    print(f"G-reactive: offset s=1/2 row moved top by {react:.3e} "
          f"(min {REACT_MIN:.0e})")
    if react < REACT_MIN:
        abort("REACT")

    # slack U + second fixed whitening + Gershgorin verdict
    U = top_mid + DELTA
    Dmid = U * np.eye(n_dim) - CMC_sym
    Drad = HRAD.copy()
    try:
        Rc = cholesky(Dmid, lower=True)
    except LinAlgError:
        abort("SLACKCHOL")
    Rci = np.linalg.inv(Rc)
    Gmid = Rci @ Dmid @ Rci.T
    Gmid_sym = (Gmid + Gmid.T) / 2.0
    # |Gmid - Gmid.T| is PURE float rounding here (Dmid is symmetric by
    # construction), so it is a legitimate rounding cover; fix batch 1
    # replaces the old floor with the CENTER_CHOL comparison-sum bound
    # (same channel as the first congruence).
    GRAD = np.abs(Rci) @ Drad @ np.abs(Rci).T \
        + np.abs(Gmid - Gmid.T) / 2.0 \
        + CENTER_CHOL * (np.abs(Rci) @ np.abs(Dmid) @ np.abs(Rci).T)
    slacks = []
    for i in range(n_dim):
        off = sum(abs(Gmid_sym[i, j]) + GRAD[i, j]
                  for j in range(n_dim) if j != i)
        slacks.append(Gmid_sym[i, i] - GRAD[i, i] - off)
    slacks = np.array(slacks)
    print("row slacks (dd):", " ".join(f"{s:+.3e}" for s in slacks))
    print(f"min slack = {slacks.min():+.3e}; U = {U:+.12e}")
    if slacks.min() > 0.0:
        print(f"PASS-IV{cl['tag']}: DEPENDENCY-SAFE certified "
              f"top(A+P)|_V <= {U:+.6e} (+ {EPS:.0e} inherited channels "
              f"-> {U + EPS:+.6e}) < 0")
        verdict = f"PASS-IV{cl['tag']}"
    else:
        print(f"STRADDLE-IV{cl['tag']}: diagonal dominance fails; "
              f"certified (non-strict) top <= {U:+.6e} NOT achieved; "
              f"1110/1109 float-domain certificates stand")
        verdict = f"STRADDLE-IV{cl['tag']}"
    return cl, dict(top_mid=top_mid, U=U, DELTA=DELTA, EPS=EPS,
                    slacks=slacks.tolist(), verdict=verdict,
                    Zn=Zn, L=L, Rc=Rc, M=M, G=G, R=R,
                    wM_box=wM_box, wG_box=wG_box, TRUNC=TRUNC)


def frac_out(x, widen_ulps=2):
    """Exact rational with OUTWARD float-representation widening."""
    return (Fraction(x) - Fraction(math.ulp(x)) * widen_ulps,
            Fraction(x) + Fraction(math.ulp(x)) * widen_ulps)


results = []
for cl in CLASSES:
    results.append(certify(cl))

# ingestion bundle (1111's future rational-Cholesky consumer)
classes_out: list = []
for cl, r in results:
    entry = dict(
        A_R=cl["A_R"], N_GL=cl["N_GL"], TAU=cl["TAU"], DELTA=r["DELTA"],
        EPS_inherited=r["EPS"], top_mid=r["top_mid"], U=r["U"],
        U_outward=[str(f) for f in frac_out(r["U"])],
        verdict=r["verdict"], row_slacks=r["slacks"],
        # outward rational enclosures of the registered interval boxes
        G_lo=[[str(frac_out(r["G"][i, j] - r["wG_box"][i, j])[0])
               for j in range(K)] for i in range(K)],
        G_hi=[[str(frac_out(r["G"][i, j] + r["wG_box"][i, j])[1])
               for j in range(K)] for i in range(K)],
        M_lo=[[str(frac_out(r["M"][i, j] - r["wM_box"][i, j])[0])
               for j in range(K)] for i in range(K)],
        M_hi=[[str(frac_out(r["M"][i, j] + r["wM_box"][i, j])[1])
               for j in range(K)] for i in range(K)],
        box_channels=dict(TRUNC_entry=r["TRUNC"], WIDEN_ULPS=WIDEN_ULPS),
        # fixed float data (double-precision; the ingestion brick decides
        # its own rational outward policy for these):
        R_mid=r["R"].tolist(), G_mid=r["G"].tolist(), M_mid=r["M"].tolist(),
        null_basis_Zn=r["Zn"].tolist(), chol_L=r["L"].tolist(),
        chol_Rc=r["Rc"].tolist(),
    )
    classes_out.append(entry)
bundle = dict(record="1112", classes=classes_out)
out = os.path.join(HERE, "1112_cert.json")
with open(out, "w", encoding="utf-8") as fh:
    json.dump(bundle, fh, indent=1)
print(f"wrote {out}")
print("PER-CLASS VERDICTS:", ", ".join(r["verdict"] for _, r in results))
print("DONE")
