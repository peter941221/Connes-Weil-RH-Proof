#!/usr/bin/env python3
"""Probe the OUTER channel (I-R)oD on the EXACT prolate/Slepian carrier.

Motivation (816 verdict): the only escape left for Gate-3U is that the outer
channel (I-R)oD vanishes on the *exact* prolate spheroidal wave functions of the
true Sonin space rather than on 816's smooth-bump / Gaussian-sinc approximations.
816 leaked 0.24-0.48 and did NOT decay under band-limiting, but those functions
were approximate prolate.  This probe replaces them with the actual Slepian
sequences (discrete prolate spheroidal sequences, scipy.signal.dpss) -- the
maximal-concentration band-limited radial functions -- and asks whether the
outer channel cancels on those.

Lean status of the target (GlobalLogSoninProjection.lean:153-163): the repo
defines the Sonin space ONLY by abstract star-projections
    cc20TransportedSoninClosedSubspace U =
        cc20PositiveHalfLineClosedRange ⊓ cc20TransportedHalfLineClosedRange U
with cc20PositiveHalfLine = Set.Ici 0 (a SPATIAL/log half-line), and there are
NO explicit prolate spheroidal wave functions.  So the exact prolate carrier is
not numerically reachable from the repo's own objects; the Slepian sequences
below are the mathematically-correct OBJECT the hyper-escape named.

Method (mirrors 815 / 816): metric coframe D = T^+ (A G^-1 A^+) on the carrier
span A = (T J) [radial columns of T], G = A^+ A (carrier-restricted).  We build
a Slepian carrier B (band-limited, each element cut to radial support t>=logla),
apply D to each element, and report the fraction of D u norm lying under loglambda
(the radial complement, i.e. (I-R) leakage).  Saturation at a positive fraction
= outer channel does NOT vanish on the exact prolate carrier;  trend -> 0 as the
Slepian band narrows = the hyper-escape holds.

Run:  python3 817_outer_channel_slepian_probe.py   (WSL venv: .venv-probe)
"""
from __future__ import annotations
import numpy as np
import sys
try:
    from scipy.signal.windows import dpss
except ImportError:
    sys.exit("need scipy:  source .venv-probe/bin/activate && pip install scipy")


def shift_op(p, dt, n, sign):
    """One shift factor (I - p^-1/2 U_{sign*sh}) as an n x n matrix."""
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


def slepian_carrier(t, logla, nw, nwant):
    """Exact Slepian band-limited radial functions cut to t >= logla.

    dpss takes (length, time-bandwidth NW); we build Slepian sequences on the
    radial half-line and zero everything below logla to select the physical
    (radial-support ∩ band-limited) Sonin carrier.  Returns (len(t), nwant)
    with orthonormal-ish columns.
    """
    lo = np.searchsorted(t, logla - 1e-12)
    n = len(t)
    # Slepian sequences on the separable band-limited spectrum; the Sonin
    # carrier is maximal-concentration onto the radial half-line [logla, oo).
    # Place the dpss window as a sub-window INSIDE the radial support, hugging
    # the boundary logla, so each column is band-limited AND radial-supported.
    Lwin = max(4, int(4 * nw))
    Lwin = min(Lwin, max(4, n - lo))
    win = dpss(Lwin, nw, nwant)                          # (Kmax, Lwin); Kmax <= nwant
    ncol = win.shape[0]
    start = lo
    end = lo + Lwin
    W = np.zeros((n, ncol))
    W[start:end, :] = win.T
    W[t < logla - 1e-12, :] = 0.0                      # radial cut
    for k in range(ncol):
        nrm = np.linalg.norm(W[:, k])
        if nrm > 0:
            W[:, k] /= nrm
    return W


def main():
    primes_lists = [[2], [2, 3], [2, 3, 5]]
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
            GinvP = lambda u: A @ (Ginv @ (A.conj().T @ u))   # frame projector span(A)

            def D(u):
                # metric coframe on the carrier span:  D u = T^+ (A G^-1 A^+ u)
                return Td @ GinvP(u)

            for nw in [2, 4, 8]:
                W = slepian_carrier(t, logla, nw, nwant=6)
                rel = []
                for j in range(W.shape[1]):
                    Du = D(W[:, j])
                    o = np.linalg.norm(Du[under]); f = np.linalg.norm(Du)
                    rel.append(o / f if f > 0 else 0.0)
                mx = max(rel) if rel else 0.0
                print(f"logla={logla} pr={pr} NW={nw:2d}  max (I-R)oD leak on "
                      f"Slepian carrier: {mx:.3f}   [" + " ".join(f"{v:.3f}" for v in rel) + "]")


if __name__ == "__main__":
    main()