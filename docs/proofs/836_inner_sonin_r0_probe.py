#!/usr/bin/env python3
"""Probe 3: does a STABLE, orthogonal (Slepian-basis) R0 fix 818's degraded inner
channel, or is the 0.85-0.98 band/second number real?

Why this is new (vs 818 and 817):
  * 818 built R0 = proj(range(R) ∩ range(Q0)) by von Neumann ALTERNATING
    PROJECTION onto range(R) ∩ range(H^dag R H), with a pure-phase HT clone
    Q0. On the finite grid the two finite subspaces intersect only at {0},
    so R0 degenerated to rank-0 and the band/second channels (0.85-0.98)
    were DISCOUNTED as an artifact.
  * 817 measured the OUTER channel (I-R)D on the exact Slepian carrier and
    never touched the inner (band/second) channels because R0 was the blocker.

This probe tests the hypothesis that 818's collapse was an ARTIFACT of (a)
alternating projection and/or (b) the pure-phase Q0, not a real number.  It
replaces BOTH: it builds R0 as the ORTHOGONAL projection onto the span of the
exact Slepian (discrete prolate) basis on the radial half-line [logla, oo) --
the mathematically correct maximal-concentration Sonin object (817 §why) --
instead of an alternating-projection intersection.  It then measures the
band channel (R - R0) D on that stable R0.

Honesty: Slepian R0 is an APPROXIMATION of the analytic prolate Sonin
projection, not the repo's own object.  So a nonzero result means "the band
channel is nonzero for ANY sensible finite R0", and a near-zero result means
"818's degeneration was the artifact, and on the correct carrier the inner
channel cancels."  Both are gate-informative.

Run:  python3 836_inner_sonin_r0_probe.py   (WSL venv: .venv-probe)
"""
from __future__ import annotations
import numpy as np
import sys
try:
    from scipy.signal.windows import dpss
except ImportError:
    sys.exit("need scipy:  source .venv-probe/bin/activate")


def shift_op(p, dt, n, sign):
    sh = int(round(float(np.log(p)) / dt))
    S = np.eye(n)
    for i in range(n):
        j = i + sign * sh
        if 0 <= j < n:
            S[i, j] -= p ** -0.5
    return S


def T_matrix(primes, dt, n, sign):
    T = np.eye(n)
    for p in primes:
        T = shift_op(p, dt, n, sign) @ T
    return T


def slepian_basis(t, logla, nw, nwant):
    """Orthonormal radial half-line Slepian basis (each band-limited AND cut to
    t>=logla).  This is the finite-grid model of the analytic prolate Sonin
    carrier.  Returns (n, K) with orthonormal columns; R0 = the orthogonal
    projector onto this K-dim subspace is a well-conditioned, non-degenerate
    stand-in for the analytic R0."""
    lo = np.searchsorted(t, logla - 1e-12)
    n = len(t)
    Lwin = max(4, int(4 * nw))
    Lwin = min(Lwin, max(4, n - lo))
    win = dpss(Lwin, nw, nwant)
    ncol = win.shape[0]
    start = lo
    end = lo + Lwin
    W = np.zeros((n, ncol))
    W[start:end, :] = win.T
    W[t < logla - 1e-12, :] = 0.0
    cols = []
    for k in range(ncol):
        nrm = np.linalg.norm(W[:, k])
        if nrm > 1e-12:
            cols.append(W[:, k] / nrm)
    if not cols:
        return np.zeros((n, 0))
    Q = np.column_stack(cols)
    # orthonormalize via QR for a clean orthogonal projector
    Q, _ = np.linalg.qr(Q)
    return Q


def main():
    primes_lists = [[2], [2, 3], [2, 3, 5]]
    print("probe3: orthogonal (Slepian) R0 vs 818's alternating-projection R0")
    print("inner band channel = |(R - R0) D|/|D| ; 0 => inner closes")
    for logla in [0.0, 1.0]:
        for pr in primes_lists:
            Lt = 4.0; n = 200
            t = np.linspace(-Lt, Lt, n); dt = t[1] - t[0]
            car = np.where(t >= logla - 1e-12)[0]
            under = np.where(t < logla - 1e-12)[0]
            T = T_matrix(pr, dt, n, +1)
            Td = T_matrix(pr, dt, n, -1)
            A = T[:, car]
            G = A.conj().T @ A
            Ginv = np.linalg.inv(G + 1e-16 * np.eye(len(car)))

            def D(u):
                return Td @ (A @ (Ginv @ (A.conj().T @ u)))

            Rm = np.diag((t >= logla - 1e-12).astype(float))
            for nw in [2, 4, 8]:
                Q = slepian_basis(t, logla, nw, nwant=8)   # (n, K)
                K = Q.shape[1]
                if K == 0:
                    print(f"logla={logla} pr={pr} NW={nw}: empty Slepian basis")
                    continue
                R0 = Q @ (Q.conj().T)                       # orthogonal projector
                # sanity: R0 is a genuine projection (idempotent) & nonzero rank
                idem = np.linalg.norm(R0 @ R0 - R0)
                rank0 = int(np.linalg.matrix_rank(R0, tol=1e-9))
                # preselect carrier test points
                js = sorted(set(int(x) for x in np.linspace(0, len(car) - 1, 3)))
                res = []
                for jidx in js:
                    u = np.zeros(n); u[car[jidx]] = 1.0
                    Du = D(u); fn = np.linalg.norm(Du) + 1e-30
                    band = np.linalg.norm((Rm - R0) @ Du) / fn   # (R-R0)D
                    sonin = np.linalg.norm(R0 @ Du) / fn
                    res.append((band, sonin))
                b = np.mean([x[0] for x in res]); s = np.mean([x[1] for x in res])
                print(f"logla={logla} pr={pr} NW={nw:2d} K={K:2d} "
                      f"idem={idem:.1e} rank0={rank0}  band|(R-R0)D|={b:.3f} "
                      f"sonin|R0D|={s:.3f}")


if __name__ == "__main__":
    main()