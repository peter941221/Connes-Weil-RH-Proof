#!/usr/bin/env python3
"""1637: compact-observable test for finite-section carrier escape.

For the actual symbol, form the smallest generalized eigenvector in the
translate section used by the 1630 probe.  A fixed finite-rank projection is a
compact observable.  If the approximate kernels retained a nonzero mass under
one such fixed projection as K grows, that would be the numerical shape needed
by the formal 1636 compact-observable witness interface.  Vanishing mass is
evidence of weak escape and tells us that recentering/tightness is necessary.
"""

import os
import sys
import math

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
KS = (1, 2, 4, 8, 16, 24, 32, 48)


def bump(u):
    out = np.zeros_like(u)
    inside = (u > -1.0) & (u < 0.0)
    s = 2.0 * (u[inside] + 0.5)
    out[inside] = np.exp(1.0 - 1.0 / (1.0 - s * s))
    return out


def proj_pos(f):
    spec = np.fft.fft(np.fft.fftshift(f))
    return np.fft.ifftshift(np.fft.ifft(np.where(POS, spec, 0.0)))


def inner(f, g):
    return DXI * np.vdot(f, g)


def normalized_probe(q):
    return q / np.sqrt(max(float(np.real(inner(q, q))), 1e-300))


def orthonormalize(probes):
    q = np.column_stack(probes)
    gram = np.array([[inner(q[:, i], q[:, j])
                      for j in range(q.shape[1])]
                     for i in range(q.shape[1])])
    vals, vecs = np.linalg.eigh(0.5 * (gram + gram.conj().T))
    keep = vals > 1e-10
    invsqrt = (vecs[:, keep] / np.sqrt(vals[keep])) @ vecs[:, keep].conj().T
    return q @ invsqrt


def h_rational(x, k):
    h = np.zeros_like(x, dtype=complex)
    neg = x < 0.0
    h[neg] = np.exp(x[neg]) * x[neg] ** (k - 1) / math.factorial(k - 1)
    return h


def main():
    x = -N * DU / 2.0 + np.arange(N) * DU
    h0 = bump(x)
    H0 = np.fft.fft(np.fft.fftshift(h0)) * DU
    m_minus = np.conj(m_of_real(XI))
    # Fixed probes must not be the expanding translate section itself.  Use
    # two rational Hardy vectors, whose unbounded spatial support is outside
    # the compact bump span used to form the finite sections.
    h3 = h_rational(x, 3)
    h4 = h_rational(x, 4)
    probes = [np.fft.fft(np.fft.fftshift(h3)) * DU,
              np.fft.fft(np.fft.fftshift(h4)) * DU]
    Q = orthonormalize([normalized_probe(q) for q in probes])
    print("1637 compact-observable probe: N=%d, |xi|<=%g, dxi=%g"
          % (N, 1.0 / (2.0 * DU), DXI))
    print("fixed observable rank=%d; probes are rational k=3 and k=4"
          % Q.shape[1])
    print("+--------+--------------+--------------+--------------+--------------+")
    print("| lambda | section K    | sigma_min    | fixed K mass | max overlap  |")
    print("+--------+--------------+--------------+--------------+--------------+")
    for lam in (0.5, 1.0 / np.e, 0.2, 0.1, 0.05, 0.02, 0.01):
        c = 2.0 * np.log(lam)
        U = np.exp(2j * np.pi * c * XI) * m_minus
        for K in KS:
            Hj = [np.exp(2j * np.pi * j * XI) * H0 for j in range(K)]
            Pj = [proj_pos(U * H) for H in Hj]
            M = np.array([[inner(Pj[i], Pj[j]) for j in range(K)]
                          for i in range(K)])
            G = np.array([[inner(Hj[i], Hj[j]) for j in range(K)]
                          for i in range(K)])
            vals, vecs = eigh(0.5 * (M + M.conj().T),
                              0.5 * (G + G.conj().T),
                              subset_by_index=[0, 0])
            coeff = vecs[:, 0]
            xv = sum(coeff[j] * Hj[j] for j in range(K))
            xn = np.sqrt(max(float(np.real(inner(xv, xv))), 1e-300))
            overlaps = np.array([inner(Q[:, i], xv) / xn
                                 for i in range(Q.shape[1])])
            mass = float(np.real(np.vdot(overlaps, overlaps)))
            maxov = float(np.max(np.abs(overlaps)))
            print("| %6.3f | %12d | %12.4e | %12.4e | %12.4e |"
                  % (lam, K, np.sqrt(max(float(vals[0]), 0.0)), mass, maxov))
        print("+--------+--------------+--------------+--------------+--------------+")


if __name__ == "__main__":
    main()
