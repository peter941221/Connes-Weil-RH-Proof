"""1342 - B0a minimum-eigenvalue falsifier search on the prime-free
root-window triple-vanishing span (MODEL rig, law 65; preregistration =
docs/proofs/1342_b0a_prime_free_vanishing_class_min_eigenvalue_falsifier_preregistration.md,
committed BEFORE any digit of this script was executed, law 42).

Design (record 1342 sections 1-5): the quadratic form qw is polarized onto
a real C-infinity bump span with support guaranteed strictly inside
(-log 2 / 2, log 2 / 2) (so the square is prime-free by the committed
lemma C1SameOwnerWeil.lean:167-189); the triple vanishing at sigma in
{0, 1/2, 1} is imposed as the exact nullspace of the 3 x m constraint
matrix; the adjudicated statistic is the minimum eigenvalue of the reduced
Gram.  Verdict bands FIRE / NO-FIRE / gray are the preregistered ones.

The 1225 dictionary functions (chi, circular_conv_centered,
simpson_uniform, moment_row_mp, build_g_control, qw_terms) are copied
verbatim from 1225_positive_control_probe.py with exactly two MECHANICAL
changes (registered here, digit-identical, law-7c constants-are-DATA
preserved):
  1. the prime sieve of qw_terms is memoized per process on qmax (a pure
     function of the registered constant A_DET; the same list, the same
     arithmetic);
  2. the grid constants are rebindable module globals so gate G4 can rerun
     the identical pipeline at doubled NQ.
The anchor control is additionally evaluated at the 1225 committed
resolution (NQ = 2^15) against the value parsed at runtime from the
committed record 1225 md (never hand-typed).

Machine note: thin-SVD trap (law 7c(69)) applies twice over - the
constraint matrix is WIDE (3 x m), so nullspace extraction uses
full_matrices=True; the rank is asserted (G3a), not assumed.

FIRE escalation clause (preregistered section 5): a FIRE witness is a
CANDIDATE, never a refutation by itself; the dictionary is model-level and
RH is numerically verified to large height, so the first-order hypothesis
on any FIRE is a rig artifact.  Certifies nothing; RH NOT claimed.
"""
import json
import math
import os
import re
import time

import mpmath
import numpy as np
from scipy.integrate import simpson as _sp_simpson

mpmath.mp.dps = 80
HERE = os.path.dirname(os.path.abspath(__file__))
SMOKE = os.environ.get("P_SMOKE") == "1"

# ---------------- 1225 verbatim constants ---------------- #
LOG4PI_GAMMA = float(mpmath.log(4 * mpmath.pi) + mpmath.euler)
NEXP = 9
A_DET = NEXP + 1
QL = 28.0
NQ = 1 << (15 if SMOKE else 17)          # official grid per prereg section 1
DQ = 2 * QL / NQ
QS = (np.arange(NQ) - NQ // 2) * DQ
M_CHK = 1400


def chi1(u):
    return math.exp(-1.0 / (1.0 - u * u)) if -1.0 < u < 1.0 else 0.0


def chi(u):
    v = np.asarray(u, dtype=float)
    out = np.zeros_like(v)
    m = (v > -1.0) & (v < 1.0)
    out[m] = np.exp(-1.0 / (1.0 - v[m] ** 2))
    return out


def circular_conv_centered(p, q):
    pp = np.fft.ifftshift(p)
    qq = np.fft.ifftshift(q)
    return np.fft.fftshift(np.fft.ifft(np.fft.fft(pp) * np.fft.fft(qq))) * DQ


def simpson_uniform(y, dx):
    """BROKEN 1116-era rule, retained VERBATIM for the G1a provenance gate
    (inv9): disjoint triples skip every third subinterval (sin-on-[0,pi]
    unit test: returns 2/3 of the true value)."""
    n = len(y)
    if n % 2 == 0:
        tail = 0.5 * dx * (y[-1] + y[-2])
        y = y[:-1]
    else:
        tail = 0.0
    y3 = y.reshape(-1, 3)
    return float(tail + (dx / 3.0)
                 * (y3[:, 0] + 4.0 * y3[:, 1] + y3[:, 2]).sum())


def simpson_fixed(y, dx):
    """Standard composite Simpson (inv9 correction): weights 4-2-4-...-2-4
    on interior points of the odd-length core, end trapezoid for even
    point counts; unit-tested against sin-on-[0, pi] in preflight."""
    y = np.asarray(y, dtype=float)
    n = len(y)
    if n < 3:
        return float(np.trapezoid(y, dx=dx))
    if n % 2 == 0:
        last = 0.5 * dx * (y[-1] + y[-2])
        y = y[:-1]
    else:
        last = 0.0
    return float(last + dx / 3.0
                 * (y[0] + y[-1] + 4.0 * y[1:-1:2].sum()
                    + 2.0 * y[2:-1:2].sum()))


def moment_row_mp(z, M):
    x, w = np.polynomial.legendre.leggauss(M_CHK)
    zm = mpmath.mpc(z)
    xm = [mpmath.mpf(v) for v in x]
    wm = [mpmath.mpf(w[k]) * mpmath.mpf(chi1(x[k])) for k in range(len(x))]
    Em = [mpmath.exp(zm * xm[k]) for k in range(len(x))]
    row, powers = [], [mpmath.mpf(1)] * len(x)
    for _ in range(M):
        row.append(mpmath.fsum(wm[k] * powers[k] * Em[k]
                               for k in range(len(x))))
        powers = [powers[k] * xm[k] for k in range(len(x))]
    return row


def build_g_control(eps):
    """1225 sec.4 control builder, verbatim (anchor for gate G1)."""
    nodes = [0.5, 1.0, 1.5, 2.0]
    Ms = len(nodes)
    epsm = mpmath.mpf(eps)
    A = mpmath.zeros(Ms, Ms)
    for i, z in enumerate(nodes):
        row = moment_row_mp(complex(z) * eps, Ms)
        for m in range(Ms):
            A[i, m] = row[m] * epsm ** (m + 1)
    rhs = mpmath.matrix([mpmath.mpc(0), mpmath.mpc(0), mpmath.mpc(0),
                         mpmath.mpc(1)])
    sol = mpmath.lu_solve(A, rhs)
    res = float(mpmath.norm(A * sol - rhs) / max(mpmath.norm(rhs), 1))
    a = np.array([complex(sol[m]) for m in range(Ms)])
    base = chi(QS / eps)
    corr = np.zeros(NQ, dtype=complex)
    xp = np.ones_like(QS)
    for am in a:
        corr += am * xp * base
        xp = xp * QS
    h = corr
    for _ in range(NEXP):
        h = circular_conv_centered(h, base)
    g = h * np.exp(QS / 2)
    peak = float(np.abs(g).max())
    if peak > 0:
        g = g / peak
    return g, dict(residual=res, max_abs_a=float(np.abs(a).max()), eps=eps)


_PRIMES_CACHE: dict[int, np.ndarray] = {}


def _primes_upto(qmax: int) -> np.ndarray:
    """Memoized prime list (mechanical change 1; same odd-sieve as 1225)."""
    if qmax in _PRIMES_CACHE:
        return _PRIMES_CACHE[qmax]
    N = (qmax - 1) // 2
    sieve = np.ones(N, dtype=bool)
    sieve[0] = False
    for p in range(3, int(math.isqrt(qmax)) + 1, 2):
        if sieve[(p - 1) // 2]:
            sieve[(p * p - 1) // 2::p] = False
    out = np.concatenate(([2], np.nonzero(sieve)[0] * 2 + 1))
    _PRIMES_CACHE[qmax] = out
    return out


def qw_terms(g, fixed: bool = True):
    """qw(g) = pole - arch - prime of F = g (*) g~* (1225 machinery,
    verbatim arithmetic; prime list memoized - same values).
    inv9: fixed=True uses simpson_fixed (the adjudicating kernel);
    fixed=False reproduces the broken 1225 arch (G1a provenance only)."""
    simp = simpson_fixed if fixed else simpson_uniform
    cvec = np.conj(g[(-np.arange(NQ)) % NQ])
    F = circular_conv_centered(g, cvec)
    f0 = float((np.abs(g) ** 2).sum() * DQ)
    pos0 = NQ // 2
    yp = QS[pos0:]
    Fp = F[pos0:]
    Fm = F[(NQ - np.arange(pos0, NQ)) % NQ]
    num = np.exp(yp / 2) * (Fp + Fm) - 2 * f0
    integ = np.empty_like(num)
    integ[1:] = num[1:] / (2 * np.sinh(yp[1:]))
    integ[0] = f0 / 2.0
    tail = f0 * math.log(math.tanh(yp[-1] / 2))
    arch = LOG4PI_GAMMA * f0 + simp(integ.real, DQ) + tail
    qmax = int(math.exp(2.0 * A_DET))
    primes = _primes_upto(qmax)
    lq = np.log(primes.astype(float))
    psum = float((lq / np.sqrt(primes) * (
        np.interp(lq, QS, F.real) + np.interp(-lq, QS, F.real))).sum())
    for pr in primes:
        pr = int(pr)
        if pr * pr > qmax:
            break
        pk, lp = pr * pr, math.log(pr)
        while pk <= qmax:
            lv = math.log(pk)
            psum += lp / math.sqrt(pk) * (
                float(np.interp(lv, QS, F.real))
                + float(np.interp(-lv, QS, F.real)))
            pk *= pr
    pole = float(np.real(np.trapezoid(np.exp(QS / 2) * F, dx=DQ)
                         + np.trapezoid(np.exp(-QS / 2) * F, dx=DQ)))
    return dict(f0=f0, arch=arch, prime=psum, pole=pole,
                qw=pole - arch - psum)


_ZERO_CACHE: list[float] = []


def zeros_up_to(T: float) -> list[float]:
    """Ascending positive ordinates of the nontrivial zeros via mpmath
    zetazero (cached; G8 spectral side, prereg inv10(b))."""
    global _ZERO_CACHE
    while not _ZERO_CACHE or _ZERO_CACHE[-1] <= T:
        k = len(_ZERO_CACHE) + 1
        g = float(mpmath.im(mpmath.zetazero(k)))
        if g > T:
            break
        _ZERO_CACHE.append(g)
    return [x for x in _ZERO_CACHE if x <= T]


def psi_spectral(g, T: float) -> float:
    """Spectral side of the explicit formula for the Hermitian square:
    2 * sum_{0 < gamma <= T} |int g e^{i gamma x} dx|^2 (multiplicity 1,
    both signs; the on-line collapse is exactly the committed W1 law
    C1SpectralOnlineNonneg.lean:50-67)."""
    gs = zeros_up_to(T)
    if not gs:
        return 0.0
    tot = 0.0
    CH = 16                                   # chunk rows of the exponent
    for j0 in range(0, len(gs), CH):
        blk = np.array(gs[j0:j0 + CH])
        L = (np.exp(1j * np.outer(blk, QS)) @ g) * DQ
        tot += 2.0 * float((L.real ** 2 + L.imag ** 2).sum())
    return tot


# G8 truncation ladder (prereg inv11): the band (drift < 1e-6 AND gap <
# max(1e-6, 1e-5*|geom|)) is UNCHANGED from inv10; only the T pair moved
# {300,400} -> {800,1200}, justified by the smoke-measured decay profile
# (witness residual +6.2e-5 at T=300 -> +2.5e-7 at T=800; control was
# already sub-budget at 300).  Evidence table in the prereg md.
T_G8_LO = 800.0
T_G8_HI = 1200.0


# ---------------- 1342 pipeline (prereg sections 2-3) ---------------- #
R_ROOT = math.log(2.0) / 2.0
DELTA = 0.01


def _set_grid(nq: int):
    global NQ, DQ, QS
    NQ = nq
    DQ = 2 * QL / NQ
    QS = (np.arange(NQ) - NQ // 2) * DQ


def build_basis(m: int):
    """Center-shrunk overlapping C-infinity bumps (prereg section 2)."""
    R = R_ROOT - DELTA
    Rp = R / (1.0 + 1.6 / m)
    s = 2.0 * Rp / m
    wb = 0.8 * s
    cs = np.array([-Rp + (j + 0.5) * s for j in range(m)])
    Ps = np.array([chi((QS - c) / wb) for c in cs])
    max_sup = float(np.max(np.where(Ps > 1e-15,
                                    np.abs(QS)[None, :], 0.0))) \
        if np.any(Ps > 1e-15) else 0.0
    return Ps, dict(R=R, Rp=Rp, spacing=s, wb=wb,
                    realized_bump_support_radius=max_sup,
                    square_radius_proxy=2.0 * max_sup)


def vanishing_matrix(Ps):
    sigmas = np.array([0.0, 0.5, 1.0])
    E = np.exp(np.outer(sigmas, QS))          # (3, NQ)
    C = DQ * (E @ Ps.T)                        # (3, m)
    return C, sigmas


def nullspace(C):
    _U, sv, Vh = np.linalg.svd(C, full_matrices=True)   # wide -> full needed
    tol = 1e-10 * sv[0]
    rk = int((sv > tol).sum())
    Z = Vh[rk:].T                              # (m, m-rk), orthonormal cols
    return Z, sv, rk


def gram_and_min(Ps, gate_logs) -> dict:
    m = len(Ps)
    B = np.zeros((m, m))
    for i in range(m):
        B[i, i] = qw_terms(Ps[i])["qw"]
        for j in range(i):
            b = (qw_terms(Ps[i] + Ps[j])["qw"]
                 - qw_terms(Ps[i] - Ps[j])["qw"]) / 4.0
            B[i, j] = B[j, i] = b
    C, sg = vanishing_matrix(Ps)
    Z, sv, rk = nullspace(C)
    # amendment inv8 (prereg): for a 3 x m constraint matrix the "s4/s1"
    # reading of G3a is vacuous (s4 == 0 by shape); the operative content
    # is rank == 3 exactly, plus a non-degeneracy condition s3/s1 > 1e-12.
    gate_logs["G3a_sv_ratio"] = float(sv[rk] / sv[0]) if rk < len(sv) else 0.0
    gate_logs["G3a_cond"] = float(sv[2] / sv[0])
    gate_logs["G3a_rank"] = rk
    # G3b: constraint residuals on the nullspace columns
    res = []
    for k in range(Z.shape[1]):
        gk = Z[:, k] @ Ps
        E = np.exp(np.outer(sg, QS))
        res.extend(np.abs(DQ * (E @ gk)) / max(np.abs(gk).max(), 1e-300))
    gate_logs["G3b_max_res"] = float(max(res))
    Gm = Z.T @ B @ Z                     # column-basis nullspace convention
    Gm = (Gm + Gm.T) / 2
    ev, W = np.linalg.eigh(Gm)
    return dict(B=B, C=C, Z=Z, Gm=Gm, ev=ev, W=W, sv=sv, rk=rk)


def main():
    t0 = time.time()
    mode = "SMOKE" if SMOKE else "OFFICIAL"
    m_bump = 8 if SMOKE else 24
    print(f"== 1342 B0a falsifier probe ({mode}) "
          f"m={m_bump} NQ={NQ} QL={QL} ==")
    out: dict = dict(record="1342", mode=mode, model=True,
               numpy=np.__version__, mpmath=mpmath.__version__,
               m_bump=m_bump, NQ=NQ, QL=QL, NEXP=NEXP, A_DET=A_DET,
               R_root=R_ROOT, DELTA=DELTA)

    # ---------- G1 anchor at the 1225 committed resolution ---------- #
    committed = None
    for cand in (os.path.join(HERE, "1225_b5_target_satisfiability_audit_"
                                   "and_positive_control_preregistration.md"),
                 os.path.join(os.getcwd(), "1225_b5_target_satisfiability_"
                              "audit_and_positive_control_preregistration.md")):
        if os.path.exists(cand):
            txt = open(cand, encoding="utf-8").read()
            vals = sorted(set(re.findall(
                r"control qw = \+([0-9][0-9.eE+-]*)", txt)))
            if vals:
                committed = float(vals[0])
                out["anchor_provenance"] = ("record 1225 md, all parsed "
                                            "values", vals)
                break
    nq1225 = 1 << 15
    g_official_nq = NQ
    if not SMOKE:
        _set_grid(nq1225)
    g_ctrl, ctrl_meta = build_g_control(0.03)
    qw_ctrl = qw_terms(g_ctrl, fixed=False)["qw"]      # G1a: broken path
    qw_ctrl_fix = qw_terms(g_ctrl)["qw"]               # corrected kernel
    if not SMOKE:
        _set_grid(g_official_nq)
    rel_anchor = abs(qw_ctrl / committed - 1.0) if committed \
        else float("nan")
    gate_g1a = committed is not None and rel_anchor < 1e-6
    # G1b: independent quadrature path for the corrected arch (prereg
    # inv10a): scipy composite Simpson on the odd-length core + the same
    # end trapezoid; must agree with simpson_fixed to < 1e-9 relative.
    pos0 = NQ // 2
    yp = QS[pos0:]
    cvec = np.conj(g_ctrl[(-np.arange(NQ)) % NQ])
    Fc = circular_conv_centered(g_ctrl, cvec)
    f0c = float((np.abs(g_ctrl) ** 2).sum() * DQ)
    numc = np.exp(yp / 2) * (Fc[pos0:]
                             + Fc[(NQ - np.arange(pos0, NQ)) % NQ]) - 2 * f0c
    integc = np.empty_like(numc)
    integc[1:] = numc[1:] / (2 * np.sinh(yp[1:]))
    integc[0] = f0c / 2.0
    tailc = f0c * math.log(math.tanh(yp[-1] / 2))
    arch_sp = LOG4PI_GAMMA * f0c + float(_sp_simpson(
        integc.real[:-1], dx=DQ)) \
        + 0.5 * DQ * (integc.real[-1] + integc.real[-2]) + tailc
    arch_fx = LOG4PI_GAMMA * f0c + simpson_fixed(integc.real, DQ) + tailc
    g1b_dev = abs(arch_sp - arch_fx) / max(abs(arch_fx), 1e-300)
    gate_g1b = g1b_dev < 1e-9
    print(f"G1a provenance (broken rule): recomputed {qw_ctrl:+.9e} vs "
          f"committed {committed!r}  rel {rel_anchor:.2e}  "
          f"[{'PASS' if gate_g1a else 'FAIL'}]")
    print(f"G1b corrected control qw = {qw_ctrl_fix:+.9e}  "
          f"(independent-path arch dev {g1b_dev:.2e})  "
          f"[{'PASS' if gate_g1b else 'FAIL'}]")
    out.update(control_qw=committed, control_qw_fixed=qw_ctrl_fix,
               control_qw_broken_recomputed=qw_ctrl,
               control_committed=(committed if committed is not None
                                  else float("nan")),
               control_rel=rel_anchor, ctrl_meta=ctrl_meta,
               G1b_arch_dev=g1b_dev)
    # G8 on the control (inv10b + inv11): geometric (corrected) vs spectral
    s800c, s1200c = psi_spectral(g_ctrl, T_G8_LO), psi_spectral(g_ctrl, T_G8_HI)
    g8c_ok = (abs(s1200c - s800c) < 1e-6
              and abs(qw_ctrl_fix - s800c) < max(1e-6, 1e-5 * abs(qw_ctrl_fix)))
    print(f"G8 control: geom {qw_ctrl_fix:+.9e} vs spect({T_G8_LO:.0f}) "
          f"{s800c:+.9e} gap {abs(qw_ctrl_fix - s800c):.2e} "
          f"drift {abs(s1200c-s800c):.2e} [{'PASS' if g8c_ok else 'FAIL'}]")

    # ---------- main pipeline at official grid ---------- #
    gates: dict = {}
    Ps, bmeta = build_basis(m_bump)
    sigmas = np.array([0.0, 0.5, 1.0])
    r = gram_and_min(Ps, gates)
    lam = float(r["ev"][0])
    out.update(basis=bmeta, lambda_min=lam,
               lambda2=float(r["ev"][1]),
               eig_spectrum=[float(x) for x in r["ev"]],
               G3a_rank=r["rk"], G3a_sv_ratio=gates["G3a_sv_ratio"],
               G3a_cond=gates["G3a_cond"],
               G3b_max_res=gates["G3b_max_res"],
               gram_diag_span=[float(np.diag(r["B"]).min()),
                               float(np.diag(r["B"]).max())])
    print(f"lambda_min(Gm) = {lam:+.9e}   lambda_2 = {r['ev'][1]:+.6e}   "
          f"rank {r['rk']}/3   sv-ratio {gates['G3a_sv_ratio']:.2e}   "
          f"null-res {gates['G3b_max_res']:.2e}")

    # ---------- witness ---------- #
    v = r["W"][:, 0]
    q = r["Z"] @ v
    gstar = q @ Ps
    peak = float(np.abs(gstar).max())
    gstar = gstar / peak
    q = q / peak
    wqw = qw_terms(gstar)
    idx = np.abs(QS)[np.abs(gstar) > 1e-15]
    realized_r = float(idx.max()) if idx.size else 0.0
    E = np.exp(np.outer(sigmas, QS))
    van = np.abs(DQ * (E @ gstar))
    gate_g2 = realized_r <= bmeta["R"] + 1e-12
    gate_g3a = (r["rk"] == 3 and gates["G3a_sv_ratio"] < 1e-10
                and gates["G3a_cond"] > 1e-12)
    gate_g3b = gates["G3b_max_res"] < 1e-9
    g6_rel = abs((q @ r["B"] @ q) - wqw["qw"]) / (1.0 + abs(wqw["qw"]))
    gate_g6 = g6_rel < 1e-9
    gate_g7 = abs(wqw["prime"]) < 1e-9
    # G5: Gram-vs-operator on 3 fixed seeds over the FULL span
    g5 = 0.0
    for seed in (1342001, 1342002, 1342003):
        rng = np.random.default_rng(seed)
        qq = rng.standard_normal(len(Ps))
        gq = qq @ Ps
        qwd = qw_terms(gq)["qw"]
        g5 = max(g5, abs(qq @ r["B"] @ qq - qwd) / (1.0 + abs(qwd)))
    gate_g5 = g5 < 1e-9
    print(f"witness: peak-rescaled, r={realized_r:.6f} (bound "
          f"{bmeta['R']:.6f})  direct qw = {wqw['qw']:+.9e}  "
          f"prime {wqw['prime']:+.2e}  vanishing {van.max():.2e}")
    print(f"G2 support {'PASS' if gate_g2 else 'FAIL'}   "
          f"G3a {'PASS' if gate_g3a else 'FAIL'}   "
          f"G3b {'PASS' if gate_g3b else 'FAIL'}   "
          f"G5 gram-identity {g5:.2e} {'PASS' if gate_g5 else 'FAIL'}   "
          f"G6 witness {wqw['qw']:+.2e} rel-check "
          f"{'PASS' if gate_g6 else 'FAIL'}   "
          f"G7 prime-free {'PASS' if gate_g7 else 'FAIL'}")

    # G8 on the witness (inv10b + inv11): explicit-formula fidelity of the
    # corrected dictionary on the ACTUAL adjudicated object
    s800w, s1200w = psi_spectral(gstar, T_G8_LO), psi_spectral(gstar, T_G8_HI)
    g8w_gap = abs(wqw["qw"] - s800w)
    g8w_drift = abs(s1200w - s800w)
    gate_g8w = (g8w_drift < 1e-6
                and g8w_gap < max(1e-6, 1e-5 * abs(wqw["qw"])))
    print(f"G8 witness: geom {wqw['qw']:+.9e} vs spect({T_G8_LO:.0f}) "
          f"{s800w:+.9e} gap {g8w_gap:.2e} drift {g8w_drift:.2e} "
          f"[{'PASS' if gate_g8w else 'FAIL'}]")

    # ---------- G4 resolution doubling ---------- #
    _set_grid(2 * g_official_nq)
    Ps2, _bmeta2 = build_basis(m_bump)
    gates2: dict = {}
    r2 = gram_and_min(Ps2, gates2)
    lam2 = float(r2["ev"][0])
    _set_grid(g_official_nq)
    d_lam = abs(lam2 - lam)
    gate_g4 = d_lam < 1e-8
    print(f"G4 doubling: lambda_min {lam:+.9e} -> {lam2:+.9e}  "
          f"delta {d_lam:.2e}  [{'PASS' if gate_g4 else 'FAIL'}]")
    out.update(witness=dict(qw=wqw["qw"], pole=wqw["pole"],
                            arch=wqw["arch"], prime=wqw["prime"],
                            f0=wqw["f0"], realized_radius=realized_r,
                            vanishing_max=float(van.max()),
                            peak=peak, coeff_norm=float(np.abs(q).max())),
               G4_lambda_min_at_doubled_grid=lam2, G4_delta=d_lam,
               G5_max=g5, G6_rel=g6_rel)

    allg = dict(G1a=gate_g1a, G1b=gate_g1b, G2=gate_g2, G3a=gate_g3a,
                G3b=gate_g3b, G4=gate_g4, G5=gate_g5, G6=gate_g6,
                G7=gate_g7, G8c=g8c_ok, G8w=gate_g8w)
    out["gates"] = {k: bool(v) for k, v in allg.items()}
    out["G8"] = dict(T_lo=T_G8_LO, T_hi=T_G8_HI,
                     control_gap=float(abs(qw_ctrl_fix - s800c)),
                     control_drift=float(abs(s1200c - s800c)),
                     witness_gap=float(g8w_gap),
                     witness_drift=float(g8w_drift))
    print("gates " + " ".join(f"{k}={'T' if v else 'F'}"
                              for k, v in allg.items()))

    # ---------- verdict (preregistered bands) ---------- #
    if not SMOKE:
        if not all(allg.values()):
            verdict = "ABORTED-UNINFORMATIVE"
        elif lam <= -1e-6 and wqw["qw"] <= -1e-6:
            verdict = "FIRE"
        elif lam >= -1e-8:
            verdict = "NO-FIRE"
        else:
            verdict = "ABORTED-UNINFORMATIVE (gray band)"
        out["verdict"] = verdict
        print(f"VERDICT: {verdict}")
        fname = os.environ.get("P_OUT", "1342_falsifier_results.json")
    else:
        out["verdict"] = "SMOKE-ONLY"
        fname = "1342_smoke_results.json"
    out["secs"] = round(time.time() - t0, 1)
    with open(os.path.join(HERE, fname), "w") as fh:
        json.dump(out, fh, indent=1)
    if SMOKE:
        print("SMOKE-MACHINERY-GREEN")
    print(f"DONE 1342  ({mode}, {out['secs']}s, MODEL, certifies nothing, "
          "RH NOT claimed)")


if __name__ == "__main__":
    main()
