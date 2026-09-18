#!/usr/bin/env python3
"""1634 part 2: the two regimes of the defect at small lambda.

Part A (rational family, unbounded support): check that D_real / D_model is a
CONSTANT as |c| = 2|log lambda| grows, for k = 2, 3, 4.  The 1633 tail law
predicted lambda^{2k-1}; the position law predicts D_model and the data of
part 1 showed the real exponent matching the MODEL exponent 2 - 2(k-1)/|c|.

TRANSLATE DIRECTION: the family shifts RIGHT, s in {0, 1, ..., 8}.  The model
defect of h(.-s) is the mass of h on (-inf, c - s), so it DECREASES in s;
leftward shifts are the unfavourable direction and a leftward-only family is
a bad family that pollutes the ratio (the first draft used s <= 0 and its
k = 2 row broke at |c| ~ 14 for that reason).  Both the min over s and the
single vector s = 0 are reported.

Part B (compactly supported family, the 1627 regime): for a C^inf bump of
width W translated right, the MODEL defect is 0 once the shifted support
clears the threshold, so whatever the real symbol reads there is the pure
m-induced residual -- the quantity 1627 proves is never zero for finite-type
data and that O1/O3 must control.  NOTE (rig limit, 1634): this residual is
NOT resolvable by an FFT-modulation rig -- the model itself reads ~1e-9 for
W = 1 and ~1e-15 for W = 4, i.e. the fractional-shift aliasing floor of
non-band-limited data, not zero.  Only the rational family (algebraic
spectrum, live model floor) gives resolvable readings.

Run: WSL, uv run --with numpy --with scipy --with mpmath python <this file>.
"""

import numpy as np
import scipy.special as sp
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rh_symbol_num import m_of_real  # noqa: E402
from carrier_floor_1633 import bump_of_width  # noqa: E402

NBITS = int(sys.argv[1]) if len(sys.argv) > 1 else 15
N = 1 << NBITS
DU = 1.0 / 128.0
XI = np.fft.fftfreq(N, d=DU)
X = np.fft.fftfreq(N, d=1.0 / (N * DU))
NEG = X < 0.0


def h_of_k(k):
    h = np.zeros(N, dtype=complex)
    m = X < 0.0
    h[m] = np.exp(X[m]) * X[m] ** (k - 1) / float(sp.factorial(k - 1))
    return h


def defect(U, h):
    hhat = np.fft.fft(h) * DU
    u = np.fft.ifft(U * hhat) / DU
    return float(np.linalg.norm(u[NEG]) / np.linalg.norm(u))


def main():
    m_minus = np.conj(m_of_real(XI))
    print("rig: N = %d, du = %g, |xi| <= %g" % (N, DU, 1 / (2 * DU)))
    print()
    print("=== A. rational family: is real/model constant as |c| grows? ===")
    for k in (2, 3, 4):
        print()
        print("k = %d   (tail law predicts slope 2k-1 = %d; position law 2 - 2(k-1)/|c|)"
              % (k, 2 * k - 1))
        print("+---------+---------+--------------+--------------+----------+---------+---------+")
        print("| lambda  |  |c|    |  D_model     |  D_real      | ratio    | p_model | p_real  |")
        print("+---------+---------+--------------+--------------+----------+---------+---------+")
        prev = None
        for lam in (0.01, 0.005, 0.002, 0.001, 0.0005):
            c = 2.0 * np.log(lam)
            U = np.exp(2j * np.pi * c * XI)
            bm, br = np.inf, np.inf
            dm0 = dr0 = float("nan")
            for s in (0, 1, 2, 3, 4, 6, 8):
                h = np.roll(h_of_k(k), int(round(s / DU)))
                dm = defect(U, h)
                dr = defect(U * m_minus, h)
                if s == 0:
                    dm0, dr0 = dm, dr
                bm = min(bm, dm)
                br = min(br, dr)
            pm = pr = float("nan")
            if prev is not None:
                l0, m0, r0 = prev
                if bm > 0 and m0 > 0:
                    pm = np.log(bm / m0) / np.log(lam / l0)
                if br > 0 and r0 > 0:
                    pr = np.log(br / r0) / np.log(lam / l0)
            prev = (lam, bm, br)
            print("| %7.4f | %7.3f | %12.4e | %12.4e | %8.4f | %7.2f | %7.2f |"
                  % (lam, -c, bm, br, br / bm, pm, pr))
            print("|         |  s = 0  | %12.4e | %12.4e | %8.4f |         |         |"
                  % (dm0, dr0, dr0 / dm0))
        print("+---------+---------+--------------+--------------+----------+---------+---------+")

    print()
    print("=== B. compact support: the pure m-induced residual (model defect = 0) ===")
    print("bump of width W translated to s in {0,...,-8}; model reads exactly 0")
    print("once |c| > W + 8, so D_real below is the residual 1627 proves nonzero.")
    for W in (1.0, 4.0):
        print()
        print("W = %g" % W)
        print("+---------+---------+--------------+------------------+")
        print("| lambda  |  |c|    |  D_model     |  D_real          |")
        print("+---------+---------+--------------+------------------+")
        h0 = bump_of_width(W) * np.sqrt(DU)
        for lam in (0.01, 0.005, 0.002, 0.001, 0.0005):
            c = 2.0 * np.log(lam)
            U = np.exp(2j * np.pi * c * XI)
            bm, br = np.inf, np.inf
            for s in (0, 1, 2, 3, 4, 6, 8):
                h = np.roll(h0, int(round(s / DU)))
                bm = min(bm, defect(U, h))
                br = min(br, defect(U * m_minus, h))
            print("| %7.4f | %7.3f | %12.4e | %16.6e |" % (lam, -c, bm, br))
        print("+---------+---------+--------------+------------------+")


if __name__ == "__main__":
    main()