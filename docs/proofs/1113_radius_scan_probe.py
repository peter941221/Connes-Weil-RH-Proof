"""1113 - the (a,8) radius-family certified scan: cells (3,8), (5,8).

Pre-registration: 1113_radius_scan_preregistration.md (committed before
this run).  Cell machinery is 1112 VERBATIM (including its fix batch 1
CENTER_CHOL channel) plus the registered U >= 0 guard (STRADDLE without
attempting the second whitening).  Extra columns (measurement, no gate):
A+P = -Z identity diagnostic via the 1105 bundle p6_weil.zero_gram
(Nz=600 + tail reference) and the 1106 F.6 pure-arch column via f0.tops
with the committed anchor-drift check.  Window classes only; the Lean
gate Prop is NOT discharged; RH is not claimed.
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
BUNDLE = os.path.join(HERE, "1105_weil_identity_bundle")

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

# registered 1113 s0/s1: pin bands + cells
PIN_BAND = {3.0: (9.7e-09, 3.9e-08), 5.0: (1.7e-12, 7.0e-12)}
D_BAND_ABS = 1e-10                   # identity diagnostic absolute band

CLASSES = [
    dict(tag="38", A_R=3.0, N_GL=512, TAU=1e-17, DELTA=4.0e-09, EPS=1e-10),
    dict(tag="58", A_R=5.0, N_GL=512, TAU=1e-20, DELTA=7.0e-13, EPS=1e-10),
]

# committed F.1 anchors (1106/1107 literals) for the f0 drift check
F1_ANCHORS = {
    (2.0, 8): dict(top_arch=0.854466, min_prime=-0.858729,
                    top_arch_minus_prime=1.712992),
    (4.0, 8): dict(top_arch=1.781109, min_prime=-1.781212,
                    top_arch_minus_prime=3.562321),
}


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
    """Returns arb matrices (G_TAB, R_MAT, M_MAT) via the 1108/1112 rules."""
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
        if (ky + 1) % 256 == 0:
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
    nsh = len(PRIMES)
    for iq, q in enumerate(PRIMES):
        xi = IV(IV(q).iv.log())
        w = IV(von_mangoldt_log(q)) / IV(IV(q).iv.sqrt())
        tab = t_table(-xi)             # phi_j(t + xi)
        for i in range(K):
            for j in range(K):
                P_MAT[i, j] = P_MAT[i, j] + (IV(2) * w) * tab[i, j]
        if (iq + 1) % 512 == 0:
            print(f"  [{A_R:.0f}] shifts {iq + 1}/{nsh}")

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


def symev(m):
    return eigh((m + m.T) / 2.0, eigvals_only=True)


# ==================================================== certification (1112)
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

    CENTER_CHOL = 4.0 * np.finfo(float).eps          # 1112 fix batch 1
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
          f"{symev(Pz)[0]:.3e}; "
          f"||L^-1||_2^2 = {1.0 / symev(Pz)[0]:.3e}")
    band = PIN_BAND[A_R]
    in_band = -band[1] <= top_mid <= -band[0]
    print(f"pin band [{-band[1]:.2e}, {-band[0]:.2e}]: "
          f"{'BAND-OK' if in_band else 'BAND-VIOLATION (report, no patch)'}")

    # G-xcheck canary (law 50/53): symmetrized generalized route
    Mz = Zn.T @ M @ Zn
    top_gen = float(eigvalsh((Mz + Mz.T) / 2.0, (Pz + Pz.T) / 2.0)[-1])
    d_xc = abs(top_gen - top_mid)
    print(f"G-xcheck |diff| = {d_xc:.2e} (max {XCHECK_MAX:.0e})")
    if d_xc > XCHECK_MAX:
        abort("XCHECK")

    # G-contain canary: box Gershgorin must cover the midpoint's own top
    lo_d = np.diag(CMC_sym) - HRAD.diagonal()
    hi_off = np.abs(CMC_sym) + HRAD
    np.fill_diagonal(hi_off, 0.0)
    gg_hi = float(np.max(np.diag(CMC_sym) + HRAD.diagonal() + hi_off.sum(1)))
    if not (lo_d.min() <= top_mid <= gg_hi):
        print(f"containment violated: box gg-range [{lo_d.min():.2e}, "
              f"{gg_hi:.2e}] vs top {top_mid:.2e}")
        abort("CONTAIN")

    # G-reactive canary (law 54): load-bearing row offset must move top
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

    # slack U + second fixed whitening + Gershgorin verdict (1113 guard:
    # U >= 0 => STRADDLE directly, no second whitening attempted)
    U = top_mid + DELTA
    Rc = None
    slacks = None
    if U >= 0.0:
        print(f"DELTA wider than realized pin (U = {U:+.3e} >= 0) -> "
              f"STRADDLE-IV{cl['tag']}")
        verdict = f"STRADDLE-IV{cl['tag']}"
    else:
        Dmid = U * np.eye(n_dim) - CMC_sym
        Drad = HRAD.copy()
        try:
            Rc = cholesky(Dmid, lower=True)
        except LinAlgError:
            abort("SLACKCHOL")
        Rci = np.linalg.inv(Rc)
        Gmid = Rci @ Dmid @ Rci.T
        Gmid_sym = (Gmid + Gmid.T) / 2.0
        GRAD = np.abs(Rci) @ Drad @ np.abs(Rci).T \
            + np.abs(Gmid - Gmid.T) / 2.0 \
            + CENTER_CHOL * (np.abs(Rci) @ np.abs(Dmid) @ np.abs(Rci).T)
        slacks = np.array([
            Gmid_sym[i, i] - GRAD[i, i]
            - sum(abs(Gmid_sym[i, j]) + GRAD[i, j]
                  for j in range(n_dim) if j != i)
            for i in range(n_dim)])
        print("row slacks (dd):", " ".join(f"{s:+.3e}" for s in slacks))
        print(f"min slack = {slacks.min():+.3e}; U = {U:+.12e}")
    # verdict selector: slack > 0 AND U + EPS < 0 (1113 s1 literal)
    if slacks is not None and slacks.min() > 0.0 and U + EPS < 0.0:
        print(f"PASS-IV{cl['tag']}: DEPENDENCY-SAFE certified "
              f"top(A+P)|_V <= {U:+.6e} (+ {EPS:.0e} inherited channels "
              f"-> {U + EPS:+.6e}) < 0")
        verdict = f"PASS-IV{cl['tag']}"
    elif slacks is not None and slacks.min() > 0.0:
        print(f"STRADDLE-IV{cl['tag']}: slack positive but U+EPS >= 0 "
              f"(DELTA + inherited channels wider than pin)")
        verdict = f"STRADDLE-IV{cl['tag']}"
    elif slacks is not None:
        print(f"STRADDLE-IV{cl['tag']}: diagonal dominance fails; "
              f"certified (non-strict) top <= {U:+.6e} NOT achieved; "
              f"1112/1110 certificates stand")
        verdict = f"STRADDLE-IV{cl['tag']}"
    print(f"float observation: top_mid = {top_mid:+.6e} "
          f"{'FLOAT-NEG-' + cl['tag'] if top_mid < 0 else 'NOT-NEG'} "
          f"(measurement, not a certificate)")
    return cl, dict(top_mid=top_mid, U=U, DELTA=DELTA, EPS=EPS,
                    slacks=None if slacks is None else slacks.tolist(),
                    verdict=verdict, band_ok=bool(in_band),
                    Zn=Zn, L=L, Rc=Rc, M=M, G=G, R=R,
                    wM_box=wM_box, wG_box=wG_box, TRUNC=TRUNC)


def frac_out(x, widen_ulps=2):
    """Exact rational with OUTWARD float-representation widening."""
    return (Fraction(x) - Fraction(math.ulp(x)) * widen_ulps,
            Fraction(x) + Fraction(math.ulp(x)) * widen_ulps)


results = []
for cl in CLASSES:
    results.append(certify(cl))

# ---------------- identity + pure-arch columns (1113 s2, measurement)
sys.path.insert(0, BUNDLE)
import f0          # noqa: E402
import p6_weil     # noqa: E402

print("\n---- f0 anchor drift (committed F.1 anchors) ----")
drift = 0.0
for (a, kk), ref in F1_ANCHORS.items():
    r = f0.tops(a, kk)
    for key, val in ref.items():
        drift = max(drift, abs(r[key] - val))
print(f"f0 anchor drift = {drift:.2e} (abort > 2e-3)")
if drift > 2e-3:
    abort("ANCHOR")

print("\n---- identity A+P=-Z + arch column at the scan radii ----")
ident = {}
for cl, r in results:
    a = cl["A_R"]
    ref = p6_weil.zero_gram(a, K, Nz=600, tail=True)
    lamZ = float(symev(ref["Z"])[0])
    D = r["top_mid"] + lamZ
    arch = f0.tops(a, K)
    ident[a] = dict(lamZ=lamZ, D=D, top_arch=arch["top_arch"],
                    min_prime=arch["min_prime"])
    band_msg = ("OK" if abs(D) <= D_BAND_ABS else
                "LARGE (known D(2)=6.4e-11, D(4)=1.6e-14; at a=5 a "
                "D/pin ratio above 1 is expected by design - cross-"
                "machine absolute comparison only, booked honestly)")
    print(f"a={a:g}: lambda_min(Z|_V) = {lamZ:+.6e}; "
          f"top_mid = {r['top_mid']:+.6e}; identity diagnostic "
          f"D = {D:+.3e} (band <= {D_BAND_ABS:.0e} absolute): {band_msg}")
    print(f"     F.6 column: top_arch = {arch['top_arch']:+.6f}, "
          f"min_prime = {arch['min_prime']:+.6f}")
mono = (ident[3.0]["top_arch"] > F1_ANCHORS[(2.0, 8)]["top_arch"]
        and ident[5.0]["top_arch"] > ident[3.0]["top_arch"]
        and ident[3.0]["top_arch"] < F1_ANCHORS[(4.0, 8)]["top_arch"])
print(f"arch monotone bracket (2<3<4<5): "
      f"{'OK' if mono else 'VIOLATION (report, no patch)'}")

# realized decay ratios (report): pin(a) := -top_mid(a)
pins = {2.0: 1.443377419559e-06, 4.0: 2.599928073740e-10}
for cl, r in results:
    pins[cl["A_R"]] = -r["top_mid"]
for lo, hi in ((2.0, 3.0), (3.0, 4.0), (4.0, 5.0)):
    if pins[hi] > 0.0 and pins[lo] > 0.0:
        print(f"r({lo:g}->{hi:g}) = {pins[hi] / pins[lo]:.3e}")
    else:
        print(f"r({lo:g}->{hi:g}) = undefined (non-positive pin: "
              f"{pins[lo]:.3e} -> {pins[hi]:.3e}; REPORT, no patch)")

# ---------------- ingestion bundle (same schema as 1112; STRADDLE cells
# carry verdict + data but NO certificate claim attaches)
classes_out: list = []
for cl, r in results:
    entry = dict(
        A_R=cl["A_R"], N_GL=cl["N_GL"], TAU=cl["TAU"], DELTA=r["DELTA"],
        EPS_inherited=r["EPS"], top_mid=r["top_mid"], U=r["U"],
        U_outward=[str(f) for f in frac_out(r["U"])],
        verdict=r["verdict"], pin_band_ok=r["band_ok"],
        row_slacks=r["slacks"],
        G_lo=[[str(frac_out(r["G"][i, j] - r["wG_box"][i, j])[0])
               for j in range(K)] for i in range(K)],
        G_hi=[[str(frac_out(r["G"][i, j] + r["wG_box"][i, j])[1])
               for j in range(K)] for i in range(K)],
        M_lo=[[str(frac_out(r["M"][i, j] - r["wM_box"][i, j])[0])
               for j in range(K)] for i in range(K)],
        M_hi=[[str(frac_out(r["M"][i, j] + r["wM_box"][i, j])[1])
               for j in range(K)] for i in range(K)],
        box_channels=dict(TRUNC_entry=r["TRUNC"], WIDEN_ULPS=WIDEN_ULPS),
        R_mid=r["R"].tolist(), G_mid=r["G"].tolist(), M_mid=r["M"].tolist(),
        null_basis_Zn=r["Zn"].tolist(), chol_L=r["L"].tolist(),
        chol_Rc=None if r["Rc"] is None else r["Rc"].tolist(),
    )
    classes_out.append(entry)
bundle = dict(record="1113", classes=classes_out,
              identity={str(a): ident[a] for a in ident})
out = os.path.join(HERE, "1113_cert.json")
with open(out, "w", encoding="utf-8") as fh:
    json.dump(bundle, fh, indent=1)
print(f"wrote {out}")
print("PER-CLASS VERDICTS:", ", ".join(r["verdict"] for _, r in results))
print("DONE")
