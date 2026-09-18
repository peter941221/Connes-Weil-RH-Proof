#!/usr/bin/env python3
"""1640: extract fixed-scale Laguerre near-kernel candidates.

This is a companion to 1639.  It reports coefficients in the original
Laguerre basis, rather than only the smallest singular value, so stability of
the candidate itself can be investigated before attempting an analytic
Gamma/Hardy readback.
"""

import sys

import numpy as np
from scipy.linalg import eigh

import carrier_laguerre_fixed_scale_1639 as L


def main():
    x = -L.N * L.DU / 2.0 + np.arange(L.N) * L.DU
    H = np.column_stack([L.fourier(L.h_laguerre(x, n)) for n in L.DEGREES])
    qraw = np.column_stack([L.fourier(L.h_rational(x, 3)),
                            L.fourier(L.h_rational(x, 4))])
    Q, _ = L.orthonormal_columns(qraw)
    symbol = np.conj(L.m_of_real(L.XI))
    print("1640 candidate extraction: N=%d, dxi=%g" % (L.N, L.DXI))
    for lam in (0.2, 0.1):
        U = np.exp(2j * np.pi * (2.0 * np.log(lam)) * L.XI) * symbol
        P = np.column_stack([L.proj_pos(U * H[:, i])
                              for i in range(H.shape[1])])
        print("=== lambda=%g ===" % lam)
        for dim in (8, 10, 12, 14):
            Hk = H[:, :dim]
            Pk = P[:, :dim]
            G = np.array([[L.inner(Hk[:, i], Hk[:, j]) for j in range(dim)]
                          for i in range(dim)])
            M = np.array([[L.inner(Pk[:, i], Pk[:, j]) for j in range(dim)]
                          for i in range(dim)])
            vals, vecs = eigh(0.5 * (M + M.conj().T),
                              0.5 * (G + G.conj().T),
                              subset_by_index=[0, 0])
            c = vecs[:, 0]
            pivot = int(np.argmax(np.abs(c)))
            c *= np.exp(-1j * np.angle(c[pivot]))
            xv = Hk @ c
            overlaps = np.array([L.inner(Q[:, i], xv) for i in range(Q.shape[1])])
            print("dim=%d sigma=%.8e obs=%.8e" %
                  (dim, np.sqrt(max(float(vals[0]), 0.0)),
                   float(np.real(np.vdot(overlaps, overlaps)))))
            for n, z in zip(L.DEGREES[:dim], c):
                print("  n=%2d  %.8e%+.8ei  |c|=%.8e" %
                      (n, z.real, z.imag, abs(z)))


if __name__ == "__main__":
    main()
