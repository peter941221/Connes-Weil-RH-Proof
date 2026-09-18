#!/usr/bin/env python3
"""1638: richer fixed-scale trial family for the carrier producer.

The 1637 bump-translate section plateaued at fixed lambda.  This probe keeps
lambda fixed while enlarging the Hardy trial family by compact bumps of several
widths and algebraic-tail rational vectors.  The fixed rank-two rational
observable from 1637 tests the compact-observable witness condition.
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
ETA = np.fft.fftfreq(N, d=DXI)
POS = ETA > 0


def inner(f, g):
    return DXI * np.vdot(f, g)


def proj_pos(f):
    spec = np.fft.fft(np.fft.fftshift(f))
    return np.fft.ifftshift(np.fft.ifft(np.where(POS, spec, 0.0)))


def bump(u):
    out = np.zeros_like(u)
    inside = (u > -1.0) & (u < 0.0)
    s = 2.0 * (u[inside] + 0.5)
    out[inside] = np.exp(1.0 - 1.0 / (1.0 - s * s))
    return out


def rational(x, k):
    out = np.zeros_like(x, dtype=complex)
    neg = x < 0.0
    out[neg] = np.exp(x[neg]) * x[neg] ** (k - 1) / math.factorial(k - 1)
    return out


def normalize(v):
    return v / np.sqrt(max(float(np.real(inner(v, v))), 1e-300))


def fourier(v):
    return np.fft.fft(np.fft.fftshift(v)) * DU


def fixed_observable_basis(x):
    q3 = normalize(fourier(rational(x, 3)))
    q4 = normalize(fourier(rational(x, 4)))
    Q = np.column_stack((q3, q4))
    G = np.array([[inner(Q[:, i], Q[:, j]) for j in range(2)]
                  for i in range(2)])
    vals, vecs = np.linalg.eigh(0.5 * (G + G.conj().T))
    return Q @ (vecs / np.sqrt(vals)) @ vecs.conj().T


def main():
    x = -N * DU / 2.0 + np.arange(N) * DU
    m_minus = np.conj(m_of_real(XI))
    Q = fixed_observable_basis(x)
    widths = (0.25, 0.5, 1.0, 2.0, 4.0, 8.0)
    vectors = []
    labels = []
    for w in widths:
        vectors.append(normalize(bump(x / w) / np.sqrt(w)))
        labels.append("bump-w%g" % w)
    for k in (2, 3, 4, 5):
        vectors.append(normalize(rational(x, k)))
        labels.append("rational-k%d" % k)
    H = [fourier(v) for v in vectors]
    print("1638 fixed-scale rich trial: N=%d, |xi|<=%g, dxi=%g"
          % (N, 1.0 / (2.0 * DU), DXI))
    print("family: " + ", ".join(labels))
    for lam in (0.2, 0.1, 0.05):
        c = 2.0 * np.log(lam)
        U = np.exp(2j * np.pi * c * XI) * m_minus
        P = [proj_pos(U * h) for h in H]
        print("=== lambda=%g ===" % lam)
        print("+------+--------------+--------------+--------------+--------------+")
        print("| dim  | sigma_min    | obs mass     | max overlap  | Gram min     |")
        print("+------+--------------+--------------+--------------+--------------+")
        for dim in (1, 2, 3, 4, 6, 8, 10):
            G = np.array([[inner(H[i], H[j]) for j in range(dim)]
                          for i in range(dim)])
            G = 0.5 * (G + G.conj().T)
            gv, Vg = np.linalg.eigh(G)
            scale = max(float(gv[-1]), 1.0)
            keep = gv > 1e-8 * scale
            Vorth = Vg[:, keep] / np.sqrt(gv[keep])
            Qtrial = np.column_stack(H[:dim]) @ Vorth
            Qproj = np.column_stack(P[:dim]) @ Vorth
            Morth = np.array([[inner(Qproj[:, i], Qproj[:, j])
                               for j in range(Qproj.shape[1])]
                              for i in range(Qproj.shape[1])])
            Morth = 0.5 * (Morth + Morth.conj().T)
            ge, V = np.linalg.eigh(Morth)
            coeff = V[:, 0]
            xv = Qtrial @ coeff
            xn = np.sqrt(max(float(np.real(inner(xv, xv))), 1e-300))
            overlaps = np.array([inner(Q[:, i], xv) / xn for i in range(2)])
            print("| %4d | %12.4e | %12.4e | %12.4e | %12.4e |"
                  % (dim, np.sqrt(max(float(ge[0]), 0.0)),
                     float(np.real(np.vdot(overlaps, overlaps))),
                     float(np.max(np.abs(overlaps))),
                     float(np.min(gv))))
        print("+------+--------------+--------------+--------------+--------------+")


if __name__ == "__main__":
    main()
