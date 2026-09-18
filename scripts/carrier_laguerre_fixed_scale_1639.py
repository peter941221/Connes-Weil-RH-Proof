#!/usr/bin/env python3
"""1639: fixed-scale carrier probe in an orthogonal Hardy-side basis.

Use the Laguerre basis h_n(x)=exp(x/2)L_n(-x) on x<0.  It is orthonormal in
L2((-inf,0]) and every Fourier transform is on the required Hardy side.  This
removes the ill-conditioned width-bump Gram matrix from 1638 and tests whether
the actual fixed-lambda defect can decrease with a genuinely expanding input
space.  A fixed rank-two rational observable records possible non-escape.
"""

import os
import sys
import math

import numpy as np
from scipy.special import eval_laguerre
from scipy.linalg import eigh

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rh_symbol_num import m_of_real  # noqa: E402

NBITS = int(sys.argv[1]) if len(sys.argv) > 1 else 15
DU_DEN = int(sys.argv[2]) if len(sys.argv) > 2 else 128
N = 1 << NBITS
DU = 1.0 / DU_DEN
DXI = 1.0 / (N * DU)
XI = np.fft.fftfreq(N, d=DU)
ETA = np.fft.fftfreq(N, d=DXI)
POS = ETA > 0
DEGREES = tuple(range(31))


def inner(f, g):
    return DXI * np.vdot(f, g)


def proj_pos(f):
    spec = np.fft.fft(np.fft.fftshift(f))
    return np.fft.ifftshift(np.fft.ifft(np.where(POS, spec, 0.0)))


def h_laguerre(x, n):
    out = np.zeros_like(x, dtype=complex)
    neg = x < 0.0
    out[neg] = np.exp(x[neg] / 2.0) * eval_laguerre(n, -x[neg])
    return out


def h_rational(x, k):
    out = np.zeros_like(x, dtype=complex)
    neg = x < 0.0
    out[neg] = np.exp(x[neg]) * x[neg] ** (k - 1) / math.factorial(k - 1)
    return out


def fourier(h):
    return np.fft.fft(np.fft.fftshift(h)) * DU


def orthonormal_columns(H):
    G = np.array([[inner(H[:, i], H[:, j]) for j in range(H.shape[1])]
                  for i in range(H.shape[1])])
    vals, vecs = np.linalg.eigh(0.5 * (G + G.conj().T))
    keep = vals > 1e-8 * max(float(vals[-1]), 1.0)
    return H @ (vecs[:, keep] / np.sqrt(vals[keep])), vals


def main():
    x = -N * DU / 2.0 + np.arange(N) * DU
    Hraw = np.column_stack([fourier(h_laguerre(x, n)) for n in DEGREES])
    # Preserve literal degree-prefix spaces. A global orthogonalization
    # followed by slicing would make dimension d depend on higher degrees.
    gram_vals = np.linalg.eigvalsh(
        0.5 * (np.array([[inner(Hraw[:, i], Hraw[:, j])
                          for j in range(Hraw.shape[1])]
                         for i in range(Hraw.shape[1])]) +
              np.array([[inner(Hraw[:, i], Hraw[:, j])
                         for j in range(Hraw.shape[1])]
                        for i in range(Hraw.shape[1])]).conj().T))
    qraw = np.column_stack([fourier(h_rational(x, 3)),
                            fourier(h_rational(x, 4))])
    Q, _ = orthonormal_columns(qraw)
    m_minus = np.conj(m_of_real(XI))
    print("1639 Laguerre fixed-scale probe: N=%d, |xi|<=%g, dxi=%g"
          % (N, 1.0 / (2.0 * DU), DXI))
    print("input degrees: " + ",".join(str(n) for n in DEGREES))
    print("+--------+------+--------------+--------------+--------------+--------------+")
    print("| lambda | dim  | sigma_min    | obs mass     | max overlap  | gram min     |")
    print("+--------+------+--------------+--------------+--------------+--------------+")
    cases = [("real", m_minus, (0.2, 0.1, 0.05, 0.02)),
             ("model", np.ones_like(m_minus), (1.0, 0.2))]
    for tag, symbol, lambdas in cases:
        print("=== symbol=%s ===" % tag)
        for lam in lambdas:
            c = 2.0 * np.log(lam)
            U = np.exp(2j * np.pi * c * XI) * symbol
            P = np.column_stack([proj_pos(U * Hraw[:, i])
                                  for i in range(Hraw.shape[1])])
            for dim in (1, 2, 3, 4, 5, 6, 8, 10, 12, 14):
                Hk = Hraw[:, :dim]
                Pk = P[:, :dim]
                G = np.array([[inner(Hk[:, i], Hk[:, j])
                               for j in range(dim)] for i in range(dim)])
                M = np.array([[inner(Pk[:, i], Pk[:, j])
                               for j in range(dim)] for i in range(dim)])
                vals, vecs = eigh(0.5 * (M + M.conj().T),
                                  0.5 * (G + G.conj().T),
                                  subset_by_index=[0, 0])
                coeff = vecs[:, 0]
                xv = Hk @ coeff
                overlaps = np.array([inner(Q[:, i], xv) for i in range(Q.shape[1])])
                gram_min = float(np.min(np.linalg.eigvalsh(
                    0.5 * (G + G.conj().T))))
                print("| %6.3f | %4d | %12.4e | %12.4e | %12.4e | %12.4e |"
                      % (lam, dim, np.sqrt(max(float(vals[0]), 0.0)),
                         float(np.real(np.vdot(overlaps, overlaps))),
                         float(np.max(np.abs(overlaps))), gram_min))
            print("+--------+------+--------------+--------------+--------------+--------------+")


if __name__ == "__main__":
    main()
