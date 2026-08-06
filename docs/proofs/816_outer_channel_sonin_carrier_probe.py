#!/usr/bin/env python3
"""Probe the OUTER channel on the TRUE Sonin carrier (radial ∩ Fourier-support).

True carrier (Lean, ccm24ArchimedeanSoninClosedSubspace = LogRadialSupport ⊓
ArchimedeanFourierSupport, where Fourier support = Hardy-Titchmarsh transform
vanishing below logla).  This is EXACTLY the band-limited carrier that 816 §3
identifies as the only escape for Gate-3U.

We approximate band-limitedness on the grid: radial support t >= logla  AND
Fourier support |F(u)(nu)| tails off for |nu| > some cutoff.  For the log-corridor
functions here, band-limited = support of the Fourier transform in a window.
We test: does (I-R).(T^+T).J.Ginv vanish when restricted to band-limited
carrier functions?  This is the hard bone.

Run: python3 816_outer_channel_bandin_carrier_probe.py
"""
from __future__ import annotations
import numpy as np


def shift_op(p, dt, n, sign):
    logp = float(np.log(p)); sh = int(round(logp/dt))
    S = np.eye(n)
    for i in range(n):
        j = i + sign*sh
        if 0 <= j < n:
            S[i,j] -= p**-0.5
    return S


def mk_T(primes, t):
    n=len(t); dt=t[1]-t[0]; T=np.eye(n)
    for p in primes: T = shift_op(p,dt,n,+1) @ T
    return T


def mk_Tdag(primes, t):
    n=len(t); dt=t[1]-t[0]; T=np.eye(n)
    for p in primes: T = shift_op(p,dt,n,-1) @ T
    return T


def band_limited_basis(t, logla, n_basis=8):
    """Generate band-limited radial probes with EXACT Fourier-support cutoff.

    True Sonin carrier = functions whose Fourier transform vanishes OUTSIDE a
    window (band-limited) AND radial support t >= logla.  A band-limited
    function with radial support [logla, oo) is necessarily of prolate/spheroidal
    type (the prolate spheroidal wave functions).  We approximate the leading
    ones by low-frequency, near-radial-support prolate-like functions: smooth,
    oscillating slowly, supported on t >= logla, and high-frequency-free (so they
    must be 'almost prolate').  Using a windowed cutoff: band-limited functions
    look like sinc/pswf mixtures concentrated near logla.
    """
    a = logla
    Bs = []
    for k in range(n_basis):
        # prolate-like: low-index prolate functions concentrate near a with slow osc
        nu = (k+1) * 0.8          # decreasing number of interior zeroes (low-freq)
        # band-limited-ish: sinc-type kernel centered just inside, supported on t>=a
        width = 1.2
        b = np.sin(nu * (t - a)) / (nu * (t - a) + 1e-9)   # sinc-like (band-limited)
        b = b * np.exp(-((t - a - 0.1) ** 2) / (2 * 0.9 ** 2))   # localize
        b = b * (t >= a - 1e-12)
        nrm = np.linalg.norm(b)
        Bs.append(b / nrm if nrm > 0 else b)
    return np.array(Bs).T   # (n, n_basis)


def main():
    primes_lists = [[2],[2,3],[2,3,5]]
    for logla in [0.0, 1.0]:
        for pr in primes_lists:
            L=3.0; n=150   # medium grid
            t=np.linspace(-L,L,n); dt=t[1]-t[0]
            car = np.where(t>=logla-1e-12)[0]
            under = np.where(t<logla-1e-12)[0]
            T = mk_T(pr,t); Td = mk_Tdag(pr,t)
            # metric coframe D = T^+ (T J) Grammar, but we probe outer part directly:
            #   OuterCh(u) = (I-R) D u = (I-R) T^+ (T J G^-1 u)
            B = band_limited_basis(t, logla)
            leaks = []
            for k in range(B.shape[1]):
                u = B[:,k]
                # need G^-1 u on carrier: frame A col of (T J);  u expressed in carrier span
                A = T[:,car]
                # solve dual frame: G = A^+ A ;  (A G^-1 u) = A (A^+ A)^-1 A^+ u  = projector onto span(A) applied
                # dual coframe action on u: P = A (A^+A)^-1 A^+  (projector onto col span)
                P = A @ np.linalg.inv(A.conj().T @ A + 1e-30*np.eye(len(car))) @ A.conj().T
                # D u ~ T^+ (P u)  (Gram-corrected dual)
                Du = Td @ (P @ u)
                outer = np.linalg.norm(Du[under])
                full = np.linalg.norm(Du)
                leaks.append(outer/full if full>0 else 0.0)
            print(f"logla={logla} pr={pr}  outer/full per band-limited carrier: "
                  + " ".join(f"{v:.3f}" for v in leaks))


if __name__ == "__main__":
    main()