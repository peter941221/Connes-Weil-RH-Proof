#!/usr/bin/env python3
"""Probe 884 (route A): physical Sonin-scale sweep of the OUTER channel.

824 measured the outer leak on the transported-Sonin frame at logla=0 across a
resolution/interval sweep and found a positive PLATEAU (~0.62, floor >=0.369):
the outer channel cannot vanish.  Here we ask a NEW question that 824 did not:
does sweeping the PHYSICAL Sonin scale lambda (Lean `lambda : CCM24SoninScale`,
the wavelength-band edge at t=logla) move the outer channel?  If the leak stays
>= c > 0 across the whole scale line, the negative is scale-robust.  If some
logla drives it near 0, that is a closure candidate for scrutiny.

Scope / hygiene (AGENT 8c): only the OUTER channel is read (it avoids the
numerically-unreachable Sonin intersection R0).  Reproduce 824's exact object
and values at logla=0 as a regression anchor before trusting any sweep.

Fidelity: the coframe D = T^+ J G^-1 with G = J^+ T^+ T J; the object agrees
with 816's coresp F"/the A-Gram-corrected dual projector used in 824.
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
    n = len(t); j0 = np.searchsorted(t, logla - 1e-12)
    Lwin = min(max(4, int(4 * nw)), max(4, n - j0))
    win = dpss(Lwin, nw, nwant); nc = win.shape[0]
    W = np.zeros((n, nc)); W[j0:j0 + Lwin, :] = win.T
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
    A = T[:, car]; G = A.conj().T @ A
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
    primes = [2, 3, 5, 7, 11, 13]
    print("=== regression anchor (logla=0, should match 824: ~0.56 L=8 n=600) ===")
    for n, Lt in [(600, 8.0), (1200, 8.0)]:
        v = outer_leak(primes, 0.0, n, Lt)
        print(f"  n={n} L={Lt:.0f}  outer={v:.4f}")
    print()
    print("=== Sonin-scale sweep: outer channel across logla ===")
    n, Lt = 1200, 8.0
    print(f"{'logla':>7} {'outer(max)':>10}")
    for logla in [-1.5, -1.2, -0.9, -0.6, -0.3, 0.0, 0.3, 0.6, 0.9, 1.2, 1.5,
                  -2.0, 2.0]:
        try:
            v = outer_leak(primes, float(logla), n, Lt)
            print(f"{logla:>7.2f} {v:>10.4f}")
        except Exception as e:
            print(f"{logla:>7.2f}  ERROR {type(e).__name__}: {e}")


if __name__ == "__main__":
    main()
