#!/usr/bin/env python3
# Record 1696 rig: the COMMITTED four-channel cutoff ledger at the detector test.
#
# Committed object (all defs read from tree; F27/F28 hand derivation, rig = CHECK):
#   endpoint operator  = J^dag K^dag G K J,   K = rootConvolution (conv by h)
#   G = (id + S^dag)^dag o D o (id + S^dag),  S = finiteEulerPulledObliqueShear
#       (= E^{-1} P_target E, pulled shear ALONE - C1G8AdjointShearGram.lean:59-66)
#   D = detectorOperator = C^dag C
#   cutoff family: B_n = fullBoundaryPositiveOperator g (cutoffLower n) (cutoffUpper n)
#       = zeroext[-c_n,-a_n] o factor[a_n,c_n]  (C1PositiveTraceWindowProducer.lean:145)
#       => diagonal model: B_n u = reflect(u) . 1_{|t| <= r_n},  r_n = cutoffRadius
#       (C1PositiveTraceCutoffAdapter.lean:31: r_n = supportRadius(g) + n + 1,
#        symmetric windows a_n = -r_n, c_n = +r_n)
#   four channels (C1G8AdjointShearGram.lean:1069-1100):
#       base(n)   = tr( Qc^dag B^dag D B Qc )
#       cross(n)  = tr( Qc^dag B^dag S D B Qc )
#       across(n) = tr( Qc^dag B^dag D S^dag B Qc )
#       fourth(n) = tr( Qc^dag B^dag S^dag D S B Qc )
#       book(n)   = base + cross + across + fourth = tr Qc^dag B^dag G B Qc
#   brick prediction (C1G8P4ReadbackSocketVacuity): book(n) >= 0 for all n,
#   lim book(n) >= 0  =>  != qw = -0.913 at the detector test.
#   heq would need lim book(n) = qw: the rig measures which channel would
#   have to book ~ -1.8 and shows none does.
# Instance: lambda* = e^{-1} (a=-1), g = even real bump supp 0.42, family {(2,1)},
# m-orientation (committed).  Grid as in heq_trace_check_1695.py.

import json
import numpy as np
from scipy.integrate import quad
from scipy.special import gamma as cgamma

TWO_PI = 2.0 * np.pi
LOG2 = float(np.log(2.0))
EULER_GAMMA = 0.57721566490153286060651209008240243


def scattering_phase(xi):
    s = 0.5 + TWO_PI * 1j * xi
    gr = np.pi ** (-0.5 * s) * cgamma(0.5 * s)
    return np.conj(gr) / gr


def bump(t, c):
    x = np.abs(np.asarray(t, dtype=float)) / c
    return np.where(x < 1.0, np.exp(-1.0 / np.maximum(1e-300, 1.0 - x * x)), 0.0)


def hardy_titchmarsh_matrix(t, xi, m):
    E = np.exp(TWO_PI * 1j * np.outer(t, xi))
    return (E * m[None, :]) @ E.T / len(t)


def shift_matrix(t, xi, b):
    E_plus = np.exp(TWO_PI * 1j * np.outer(t, xi))
    E_minus = np.exp(-TWO_PI * 1j * np.outer(t, xi))
    return (E_plus * np.exp(TWO_PI * 1j * xi * b)[None, :]) @ E_minus / len(t)


def null_space(A, svd_tol=1e-10):
    _, s, Vh = np.linalg.svd(A, full_matrices=True)
    rank = int(np.sum(s > svd_tol * (s[0] if len(s) and s[0] > 0 else 1.0)))
    return Vh.conj()[rank:, :].T


def orthonormalize(Z, tol=1e-9):
    if Z.shape[1] == 0:
        return np.zeros((Z.shape[0], 0), dtype=complex)
    U, s, _ = np.linalg.svd(Z, full_matrices=False)
    keep = s > tol * (s[0] if s[0] > 0 else 1.0)
    return U[:, keep]


def qw_value():
    """qw for the even bump: pole - arch - finite on a fine direct grid."""
    M = 4096
    tf = np.linspace(-2.0, 2.0, M)
    df = tf[1] - tf[0]
    gf = bump(tf, 0.42)
    gf /= np.sqrt(np.sum(gf * gf) * df)
    Fs = df * np.array([np.sum(gf * np.interp(tf - x, tf, gf, left=0.0, right=0.0))
                        for x in tf])
    F0 = float(Fs[np.argmin(np.abs(tf))])
    Flog2 = float(np.interp(LOG2, tf, Fs))
    F_at = lambda x: float(np.interp(x, tf, Fs, left=0.0, right=0.0))
    pole = 4.0 * quad(lambda y: F_at(y) * np.cosh(y / 2.0), 0.0, 0.84, limit=400)[0]

    def integrand(y):
        den = np.exp(y) - np.exp(-y)
        if den < 1e-12:
            return F0 / 2.0
        return (np.exp(y / 2.0) * (F_at(y) + F_at(-y)) - 2.0 * F0) / den
    arch = (np.log(4.0 * np.pi) + EULER_GAMMA) * F0 + \
        quad(integrand, 0.0, 0.84, limit=400)[0]
    finite = (LOG2 / np.sqrt(2.0)) * (2.0 * Flog2)
    return pole - arch - finite


def main():
    N, T, a, c = 1024, 16.0, -1.0, 0.42
    dt = 2.0 * T / N
    t = -T + dt * np.arange(N)
    xi = np.fft.fftfreq(N, d=dt)
    rows = t < a - 1e-12

    g = bump(t, c)
    g /= np.linalg.norm(g) * np.sqrt(dt)
    h_of_s = lambda s: bump(s, c) / (np.linalg.norm(bump(t, c)) * np.sqrt(dt))
    support_radius = c                                   # even bump

    m = scattering_phase(xi)
    H = hardy_titchmarsh_matrix(t, xi, m)
    C = dt * h_of_s(t[:, None] - t[None, :])             # conv by h (even)
    W = C.conj().T @ C                                   # detector D
    S = shift_matrix(t, xi, -LOG2)
    E = np.eye(N, dtype=complex) - (1.0 / np.sqrt(2.0)) * S
    Einv = np.linalg.inv(E)

    # carrier = meet {supp u in [a,inf)} cap {Hu in [a,inf)}  (v4 method)
    supp = ~rows
    A_s = H[np.ix_(rows, supp)]
    Q_s = null_space(A_s)
    Q_c = np.zeros((N, Q_s.shape[1]), dtype=complex)
    Q_c[np.ix_(supp, np.arange(Q_s.shape[1]))] = Q_s

    # target projection inside E-space, then shear-alone S = Einv P_target E
    Q_f = null_space(H[rows, :])
    W_cols = E @ Q_f
    nullc = null_space(W_cols[rows, :])
    Z = W_cols @ nullc
    Q_t = np.zeros_like(Z)
    Q_t[supp, :] = orthonormalize(Z[supp, :])
    P_target = Q_t @ Q_t.conj().T
    Sh = Einv @ P_target @ E                             # shear ALONE
    G = (np.eye(N) + Sh.conj().T) @ W @ (np.eye(N) + Sh.conj().T).conj().T

    # reflection (t -> -t) on the periodic half-open grid: k -> (-k) mod N.
    # Exact for k >= 1; k = 0 is the +-T wraparound alias (same circle point).
    flip = (-np.arange(N)) % N
    assert np.allclose(t[flip][1:], -t[1:])

    qw = qw_value()
    print("== four-channel cutoff ledger (COMMITTED object) ==")
    print(f"   N={N}, r_n = 0.42 + n + 1;  qw = {qw:+.6f}")
    print(f"   hcore (W-channel, no window) = "
          f"{float(np.trace(Q_c.conj().T @ W @ Q_c).real):+.6f}")
    results = []
    for n in (0, 2, 4, 8, 12, 16):
        r = support_radius + n + 1.0
        win = (np.abs(t) <= r + 1e-12).astype(float)
        Ref = np.eye(N)[flip]                            # t -> -t
        B = (win[:, None] * Ref)                         # diag(win) @ Ref
        BQ = B @ Q_c
        base = float(np.trace(BQ.conj().T @ W @ BQ).real)
        cross = float(np.trace(BQ.conj().T @ Sh @ W @ BQ).real)
        across = float(np.trace(BQ.conj().T @ W @ Sh.conj().T @ BQ).real)
        fourth = float(np.trace(BQ.conj().T @ Sh.conj().T @ W @ Sh @ BQ).real)
        book = base + cross + across + fourth
        row = dict(n=n, radius=r, base=base, cross=cross, across=across,
                   fourth=fourth, book=book)
        results.append(row)
        print(f"   n={n:2d} r={r:5.2f}: base={base:+.6f} cross={cross:+.6f} "
              f"across={across:+.6f} fourth={fourth:+.6f}  BOOK={book:+.6f}")
    print(f"   direct G readback tr(Qc^dag G Qc) = "
          f"{float(np.trace(Q_c.conj().T @ G @ Q_c).real):+.6f}  (no window)")
    print(f"   brick prediction: all BOOK >= 0; heq needs limit = qw = {qw:+.6f}")
    with open("results/1696_four_channel_ledger.json", "w") as f:
        json.dump({"qw": qw, "rows": results}, f, indent=1)
    print("saved results/1696_four_channel_ledger.json")


if __name__ == "__main__":
    main()
