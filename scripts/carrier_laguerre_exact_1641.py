#!/usr/bin/env python3
"""1641: exact Fourier-column cross-check for the Laguerre carrier probe.

For h_n(x)=exp(x/2)L_n(-x) 1_{x<0}, direct Laplace integration gives

    H_n(xi)=(-1/2-2*pi*i*xi)^n/(1/2-2*pi*i*xi)^(n+1).

This probe feeds those columns directly into the same finite-section
projection calculation as 1639/1640, removing the spatial-grid transform of
the input columns.  It is still a finite FFT calculation; its purpose is to
separate the exact Laguerre candidate from x-window truncation error.
"""

import math
import os
import sys

import numpy as np
from scipy.linalg import eigh

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rh_symbol_num import m_of_real  # noqa: E402

NBITS = int(sys.argv[1]) if len(sys.argv) > 1 else 15
DU_DEN = int(sys.argv[2]) if len(sys.argv) > 2 else 128
N = 1 << NBITS
DU = 1.0 / DU_DEN
DXI = 1.0 / (N * DU)
XI = np.fft.fftfreq(N, d=DU)
POS = np.fft.fftfreq(N, d=DXI) > 0


def inner(f, g):
    return DXI * np.vdot(f, g)


def proj_pos(f):
    spec = np.fft.fft(np.fft.fftshift(f))
    return np.fft.ifftshift(np.fft.ifft(np.where(POS, spec, 0.0)))


def exact_laguerre_column(n):
    den = 0.5 - 2j * math.pi * XI
    return (-0.5 - 2j * math.pi * XI) ** n / den ** (n + 1)


def rational_column(k):
    return (1.0 - 2j * math.pi * XI) ** (-k)


def generalized_prefix(H, P, dim):
    Hk = H[:, :dim]
    Pk = P[:, :dim]
    G = np.array([[inner(Hk[:, i], Hk[:, j]) for j in range(dim)]
                  for i in range(dim)])
    M = np.array([[inner(Pk[:, i], Pk[:, j]) for j in range(dim)]
                  for i in range(dim)])
    vals, vecs = eigh(0.5 * (M + M.conj().T),
                      0.5 * (G + G.conj().T), subset_by_index=[0, 0])
    return math.sqrt(max(float(vals[0]), 0.0)), vecs[:, 0], G


def main():
    H = np.column_stack([exact_laguerre_column(n) for n in range(31)])
    Qraw = np.column_stack([rational_column(3), rational_column(4)])
    qG = np.array([[inner(Qraw[:, i], Qraw[:, j]) for j in range(2)]
                   for i in range(2)])
    qvals, qvecs = np.linalg.eigh(0.5 * (qG + qG.conj().T))
    Q = Qraw @ (qvecs / np.sqrt(qvals))
    print("1641 exact Laguerre Fourier probe: N=%d, dxi=%g" % (N, DXI))
    print("+--------+------+--------------+--------------+--------------+")
    print("| lambda | dim  | sigma_min    | obs mass     | gram min     |")
    print("+--------+------+--------------+--------------+--------------+")
    mminus = np.conj(m_of_real(XI))
    for tag, symbol, lambdas in (
            ("real", mminus, (0.2, 0.1, 0.05, 0.02)),
            ("model", np.ones_like(mminus), (1.0, 0.2))):
        print("=== symbol=%s ===" % tag)
        for lam in lambdas:
            U = np.exp(2j * math.pi * (2.0 * math.log(lam)) * XI) * symbol
            P = np.column_stack([proj_pos(U * H[:, i])
                                 for i in range(H.shape[1])])
            for dim in (8, 10, 12, 14):
                sigma, coeff, G = generalized_prefix(H, P, dim)
                xv = H[:, :dim] @ coeff
                overlaps = np.array([inner(Q[:, i], xv) for i in range(2)])
                print("| %6.3f | %4d | %12.4e | %12.4e | %12.4e |"
                      % (lam, dim, sigma,
                         float(np.real(np.vdot(overlaps, overlaps))),
                         float(np.min(np.linalg.eigvalsh(
                             0.5 * (G + G.conj().T))))))
            print("+--------+------+--------------+--------------+--------------+")


if __name__ == "__main__":
    main()
