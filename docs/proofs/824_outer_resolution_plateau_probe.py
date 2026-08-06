#!/usr/bin/env python3
"""Probe 824 (route A): does the outer-channel leak on the transported-Sonin
frame PLATEAU (true lower bound > 0) or DECAY to 0 (finite-grid artifact) as
resolution grows to infinity?

822 measured the outer leak ~0.38-0.56 on the exact transported-Sonin frame at a
single grid (n=600, L=8).  This probe runs the SAME object across a resolution
sweep (n: 200..2000) and an interval sweep (L: 4..16) and asks whether the leak

    leak(n,L) = || (I-R) o D u ||_outside / || (I-R) o D u ||

saturates at a constant `c > 0` (then 822 is a REAL lower bound: Gate-3U outer
channel cannot vanish, the route is formally negative) or falls to 0 (then 822
was a grid artifact and route A honestly expires).

The frame is the repo's proven transported-Sonin object (maps_sonin_intersection,
CCM24FiniteEulerSoninTransport.lean:69-77):  frame_k = T . (Slepian radial).

Run: WSL venv python docs/proofs/824_outer_resolution_plateau_probe.py
"""
from __future__ import annotations
import numpy as np
from scipy.signal.windows import dpss


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


def slepian_radial(t, logla, nw, nwant):
    n = len(t)
    j0 = np.searchsorted(t, logla - 1e-12)
    Lwin = min(max(4, int(4 * nw)), max(4, n - j0))
    win = dpss(Lwin, nw, nwant)
    nc = win.shape[0]
    W = np.zeros((n, nc))
    W[j0:j0 + Lwin, :] = win.T
    W[t < logla - 1e-12, :] = 0.0
    for k in range(nc):
        nz = np.linalg.norm(W[:, k])
        if nz > 0:
            W[:, k] /= nz
    return W, nc


def outer_leak(primes, logla, n, Lt):
    t = np.linspace(-Lt, Lt, n); dt = t[1] - t[0]
    under = t < logla - 1e-12
    T = T_matrix(primes, dt, n, +1); Td = T_matrix(primes, dt, n, -1)
    car = np.where(t >= logla - 1e-12)[0]
    A = T[:, car]
    G = A.conj().T @ A
    Ginv = np.linalg.pinv(G)

    def D(u):
        return Td @ (A @ (Ginv @ (A.conj().T @ u)))

    Blk, nc = slepian_radial(t, logla, nw=4, nwant=6)
    leaks = []
    for k in range(nc):
        Bt = T @ Blk[:, k]
        u = Bt / (np.linalg.norm(Bt) + 1e-30)
        Du = D(u)
        fn = np.linalg.norm(Du) + 1e-30
        leaks.append(np.linalg.norm(Du[under]) / fn)
    return max(leaks)


def main():
    print("=== Resolution sweep (transported-Sonin frame), max over 6 Slepian cols ===")
    print(f"{'n':>6} {'L=4':>7} {'L=8':>7} {'L=16':>7}")
    for n in [200, 300, 400, 600, 800, 1000, 1500, 2000]:
        row = []
        for Lt in [4.0, 8.0, 16.0]:
            # keep shift of log(61)=4.11 inside box even at L=4
            r = outer_leak([2, 3, 5, 7, 11, 13], 0.0, n, Lt)
            row.append(f"{r:.4f}")
        print(f"{n:>4} {'  '.join(row)}")
    print()
    print("=== per-family at n=2000, L=8 (largest leak already; is it a floor?) ===")
    for pr in [[2], [3], [2, 3], [2, 3, 5], [7, 11], [2, 5, 7]]:
        for log in [0.0]:
            print(f"  {str(pr):10s} logla={log}  leak={outer_leak(pr, log, 2000, 8.0):.4f}")


if __name__ == "__main__":
    main()