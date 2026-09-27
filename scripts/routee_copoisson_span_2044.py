#!/usr/bin/env python3
# routee_copoisson_span_2044.py — record 2044 (probe, verdict rules fixed
# before the run)
#
# ROUTE E first brick (record 2040 / map 109): co-Poisson transcription
# matrix on the one-copy G8-H owner span, then structure test against the
# committed Weil matrix M.
#
# k1 (support-cut): the log-variable co-Poisson pullback acts as
#
#   (S_log f)(x) = sum_{n>=1} n^{-1/2} f(x - log n) - C_f * 1,
#   C_f = integral f(y) e^{-y/2} dy,
#
# a one-sided translation lattice.  On the owner basis phi_j (supports
# [-a_j, a_j], a_max = 4.752) the translation by log n has a nonzero matrix
# element overlap_ij(log n) only for log n <= a_i + a_j <= 2 a_max = 9.504:
# the lattice tail is EXACTLY zero on the span by support algebra.  k1 reads
# the cut: contributing integers are n <= exp(a_i + a_j), the global boundary
# n <= exp(2 a_max) = 13381 — the same boundary as the record-2037 visible
# book (prime powers <= 13383), but the Route-E lattice is ALL integers.
#
# B1 (Euler-Maclaurin, hand): with the integer density e^u du in u = log n,
#   sum_{n>=1} n^{-1/2} f(x - log n) ~ integral_0^infty e^{u/2} f(x - u) du
#     = e^{x/2} integral_{-inf}^x e^{-y/2} f(y) dy
#     = C_f - e^{x/2} integral_x^inf e^{-y/2} f(y) dy,
# so the continuous exchange holds up to the right-tail remainder, which is
# identically zero for x >= a_max on compactly supported f.  This script
# measures the DISCRETE remainder structure, not the identity.
#
# B2 (structure test, verdict rules FROZEN):
#   S_ij  = sum_{n=1}^{Nmax_ij} n^{-1/2} overlap_ij(log n) - C_j * D_i,
#   overlap_ij(t) = integral phi_i^bar(x) phi_j(x - t) dx,
#   D_i = integral phi_i^bar,  C_j = integral phi_j(x) e^{-x/2} dx,
# whitened to L^2-orthonormal coordinates (G = L L^H, S~ = L^H S L^{-H},
# M~ = L^{-1} M L^{-H}; M = record-2037 qmat at dxi 0.008).
#
#   STRUCTURE-POSITIVE : least-squares residual of M~ on the algebra span
#                        {I, S~, S~^H, S~S~^H, S~^HS~, S~^2, S~^H^2}
#                        r < 1e-3 * ||M~||_F.
#   r-GENERIC          : r > 0.1 * ||M~||_F (M~ carries no co-Poisson
#                        algebra structure at this resolution).
#   otherwise          : STRUCTURE-GRAY.
#
# Also printed: nested spans {I}, {I,S,S^H}, 5-family; the commutators
# [M~,S~] and [S~,S~^H]; the anchor q = corr^H M corr vs the committed
# record-2037 value -1.111095866723678e20 at dxi 0.008; and the k0 anchor
# overlap_ij(0) vs the committed h1_gram.
#
# Non-claims: float scout (no interval arithmetic); quadrature 64-node
# Gauss with a 128-node self-check; no Lean; no producer theorem; not RH.

import json, math, os, sys, time
import numpy as np

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "scripts"))

import routea_g8h_basis_comparison_2037 as r37  # noqa: E402

DXI = 0.008
Q_ANCHOR = -1.111095866723678e20   # committed record-2037 row, dxi 0.008
GAUSS_N = 64
GAUSS_N_REF = 128

_X, _W = np.polynomial.legendre.leggauss(GAUSS_N)
_XR, _WR = np.polynomial.legendre.leggauss(GAUSS_N_REF)


def bump(x, a):
    """record-2037 phi(x/a) kernel: exp(-K/(1-(x/a)^2)) on |x| < a."""
    u = np.abs(x) / a
    out = np.zeros_like(u, dtype=float)
    m = u < 1.0
    out[m] = np.exp(-r37.K / (1.0 - u[m] ** 2))
    return out


def overlap_vec(ai, thi, aj, thj, ts, nodes, weights):
    """ov(t) = integral phi_i^bar(x) phi_j(x-t) dx, vectorized over ts >= 0.

    phi_j(x-t) nonzero on x in [t-aj, t+aj]; phi_i nonzero on [-ai, ai].
    """
    lo = np.maximum(-ai, ts - aj)
    hi = np.minimum(ai, ts + aj)
    ok = hi > lo
    out = np.zeros(len(ts), dtype=complex)
    if not np.any(ok):
        return out
    lo_k, hi_k = lo[ok], hi[ok]
    mid = 0.5 * (lo_k + hi_k)
    half = 0.5 * (hi_k - lo_k)
    x = mid[:, None] + half[:, None] * nodes[None, :]
    bi = bump(x, ai)
    bj = bump(x - ts[ok][:, None], aj)
    phase = np.exp(1j * (thj - thi) * x - 1j * thj * ts[ok][:, None])
    out[ok] = (bi * bj * phase) @ weights * half
    return out


def moments(fam):
    """D_j = integral phi_j, C_j = integral phi_j e^{-x/2} dx."""
    D = np.zeros(len(fam), dtype=complex)
    C = np.zeros(len(fam), dtype=complex)
    for j, (a, th) in enumerate(fam):
        mid, half = 0.0, a
        x = mid + half * _XR
        ph = bump(x, a) * np.exp(1j * th * x)
        D[j] = (ph @ _WR) * half
        C[j] = (ph * np.exp(-x / 2) @ _WR) * half
    return D, C


def build_S(fam, D, C, n_cap=None, pair_cap=None):
    """S_ij = sum_n n^{-1/2} overlap_ij(log n) - C_j conj-scheme D_i.

    D_i multiplies as <phi_i, 1> = conj(integral phi_i) = conj(D_i).
    """
    m = len(fam)
    S = np.zeros((m, m), dtype=complex)
    stats = {"pairs": 0, "total_translations": 0, "nmax_global": 0}
    for i in range(m):
        for j in range(m):
            if pair_cap is not None and (i >= pair_cap or j >= pair_cap):
                continue
            ai, thi = fam[i]
            aj, thj = fam[j]
            amax = ai + aj
            nmax = int(math.floor(math.exp(amax) - 1e-12))
            if n_cap is not None:
                nmax = min(nmax, n_cap)
            if nmax < 1:
                continue
            ns = np.arange(1, nmax + 1)
            ts = np.log(ns)
            ov = overlap_vec(ai, thi, aj, thj, ts, _X, _W)
            S[i, j] = (ns ** -0.5) @ ov - C[j] * np.conj(D[i])
            stats["pairs"] += 1
            stats["total_translations"] += nmax
            stats["nmax_global"] = max(stats["nmax_global"], nmax)
    return S, stats


def fit_residual(M, basis):
    """Least-squares residual of M on the complex span of basis matrices."""
    n = M.shape[0]
    A = np.stack([B.reshape(-1) for B in basis]).T
    b = M.reshape(-1)
    coef, *_ = np.linalg.lstsq(A, b, rcond=None)
    r = float(np.linalg.norm(A @ coef - b) / np.linalg.norm(b))
    return r, coef


def main():
    smoke = "--smoke" in sys.argv
    t0 = time.time()
    rho, nodes, values, fam, xw, gram, a, _, _ = r37.setup(False)
    base, _ = r37.min_h1(gram, a, np.ones(len(nodes), complex))
    corr, _ = r37.min_h1(gram, a, np.asarray(values, complex))

    # ---- committed M anchor (record-2037 qmat, dxi 0.008) -------------
    xi = np.linspace(-40, 40, int(round(80 / DXI)) + 1)
    M, support, nps = r37.qmat(xi, fam, xw, base, rho)
    q = float(np.real(corr.conj() @ M @ corr))
    anchor_q_rel = abs(q - Q_ANCHOR) / abs(Q_ANCHOR)

    # ---- k0 anchor: overlap(0) vs committed gram ----------------------
    ov0_max = 0.0
    for i, (ai, thi) in enumerate(fam):
        for j, (aj, thj) in enumerate(fam):
            ov0 = overlap_vec(ai, thi, aj, thj, np.zeros(1), _XR, _WR)[0]
            ov0_max = max(ov0_max, abs(ov0 - gram[i, j]))

    # ---- quadrature self-check on pair (0,0) --------------------------
    a0, t0_ = fam[0]
    ns_chk = np.array([2, 3, 10, 100, 1000, 13381])
    ov_a = overlap_vec(a0, t0_, a0, t0_, np.log(ns_chk), _X, _W)
    ov_b = overlap_vec(a0, t0_, a0, t0_, np.log(ns_chk), _XR, _WR)
    quad_check = float(np.max(np.abs(ov_a - ov_b) / np.maximum(np.abs(ov_b), 1e-300)))

    # ---- S build ------------------------------------------------------
    D, C = moments(fam)
    S, stats = build_S(fam, D, C,
                       n_cap=500 if smoke else None,
                       pair_cap=6 if smoke else None)
    amax_all = max(a_ for a_, _ in fam)
    book_boundary = int(math.floor(math.exp(2 * amax_all) - 1e-12))

    # ---- whiten (G = L L^H; form matrices transform as B^H . B with
    # B = L^{-H}, so both S and M go through L^{-1} . L^{-H}) ----------
    L = np.linalg.cholesky(gram)
    Linv = np.linalg.inv(L)
    LinvH = np.linalg.inv(L.conj().T)
    Sw = Linv @ S @ LinvH
    Mw = Linv @ M @ LinvH
    Mw = (Mw + Mw.conj().T) / 2
    nM = float(np.linalg.norm(Mw))

    fam7 = [np.eye(len(fam), dtype=complex), Sw, Sw.conj().T,
            Sw @ Sw.conj().T, Sw.conj().T @ Sw, Sw @ Sw, Sw.conj().T @ Sw.conj().T]
    r_full, coef = fit_residual(Mw, fam7)
    r_I, _ = fit_residual(Mw, [fam7[0]])
    r_3, _ = fit_residual(Mw, fam7[:3])
    r_5, _ = fit_residual(Mw, fam7[:5])
    comm_MS = float(np.linalg.norm(Mw @ Sw - Sw @ Mw) / nM)
    comm_SS = float(np.linalg.norm(Sw @ Sw.conj().T - Sw.conj().T @ Sw)
                    / max(float(np.linalg.norm(Sw)), 1e-300))

    if not smoke:
        if r_full < 1e-3:
            verdict = "STRUCTURE-POSITIVE"
        elif r_full > 0.1:
            verdict = "r-GENERIC"
        else:
            verdict = "STRUCTURE-GRAY"
    else:
        verdict = "SMOKE (no verdict)"

    out = {
        "record": 2044, "status": verdict, "smoke": smoke,
        "owner": "one-copy G8-H", "rho": [float(rho.real), float(rho.imag)],
        "k1": {"amax": amax_all, "boundary_integers": book_boundary,
               "support_cut_exact": True,
               "note": "translations with log n > a_i + a_j have empty "
                       "quadrature windows by support algebra; integer "
                       "lattice, not prime powers",
               "total_translations_measured": stats["total_translations"],
               "pairs_measured": stats["pairs"]},
        "anchors": {"q_h1_dxi008": q, "q_committed": Q_ANCHOR,
                    "q_rel_diff": anchor_q_rel,
                    "overlap0_vs_gram_max": float(ov0_max),
                    "quad_64_vs_128_rel": quad_check},
        "structure": {"r_identity_only": r_I, "r_span3": r_3, "r_span5": r_5,
                      "r_full7": r_full,
                      "commutator_MS_over_M": comm_MS,
                      "commutator_SSH_over_S": comm_SS,
                      "M_fro_norm_whitened": nM,
                      "coef_full7_real": [float(np.real(c)) for c in coef],
                      "coef_full7_imag": [float(np.imag(c)) for c in coef]},
        "nonclaims": ["float scout, no interval arithmetic",
                      "quadrature 64-node Gauss with 128-node self-check",
                      "smoke truncates the lattice and the pair set; "
                      "structure reading only meaningful in the full run",
                      "not a producer theorem", "not RH"],
        "seconds": round(time.time() - t0, 1),
    }
    tag = "_smoke" if smoke else ""
    path = os.path.join(ROOT, "results", "2044_copoisson_span%s.json" % tag)
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        json.dump(out, f, indent=2)
        f.write("\n")
    print(json.dumps({k: out[k] for k in
                      ("status", "k1", "anchors", "structure", "seconds")},
                     indent=1))
    print("RESULT", path)


if __name__ == "__main__":
    main()
