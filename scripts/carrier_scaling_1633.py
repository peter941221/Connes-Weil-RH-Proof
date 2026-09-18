#!/usr/bin/env python3
"""1633 (map 043 item 3): the lambda-scaling law of the carrier defect.

Object (committed base, 1629 sec 3; probe form of 1630 sec 2):

    carrier(l) != {0}  <=>  exists H in H^2(C_+) \\ {0} with P_{x<0}(U_l H) = 0,
    U_l(xi) = e^{4 pi i (log l) xi} m(-xi),  m(xi) = Gamma_R(1/2-2 pi i xi)/Gamma_R(1/2+2 pi i xi),

transform dictionary F(h)(xi) = INT h(x) e^{-2 pi i x xi} dx, so that

    H^2(C_+) = {F h : supp h in (-inf, 0]}    (the x < 0 side),
    H^2(C_-) = {F h : supp h in [0, inf)}     (the x > 0 side).

For H in H^2(C_+) put D(H) = ||P_{x<0}(U_l H)|| / ||U_l H|| (scale invariant).
The carrier is nontrivial at scale l iff some nonzero H in H^2(C_+) has D = 0.
This rig measures

    sigma_min(l) = min over a finite pixel span of D,

for two families of unit-norm indicator pixels:
    A: cells of width 1/16 on [-8, 0]    (128 cells: fine near the origin),
    B: cells of width 1/8  on [-48, 0]   (384 cells: long reach).
The lambda grid is |c| = 2|log l| = j * du with j an integer, so the
modulation e^{2 pi i c xi} is an exact sample shift in x: no interpolation
error anywhere in the rig.

Validation (must hold to roundoff):
    model m := 1, l = e^{-1}: the exact witness h = 1_{[-2,0]} is a pixel union,
        so sigma_min = 0;
    model m := 1, l = 1: U = 1, every pixel has full defect, sigma_min = 1.
Every real reading is therefore quoted as (object value, floor, exact-1
control), not as a bare float.  Run: WSL,
uv run --with numpy --with scipy --with mpmath python <this file>.
"""

import numpy as np
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rh_symbol_num import m_of_real  # noqa: E402

NBITS = int(sys.argv[1]) if len(sys.argv) > 1 else 15
DU = 1.0 / 128.0
N = 1 << NBITS
XI = np.fft.fftfreq(N, d=DU)                 # |xi| <= 64
DXI = 1.0 / (N * DU)
X = np.fft.fftfreq(N, d=DXI)                 # spacing DU, extent +-N*DU/2
NEG = X < 0.0
NPIX = int(NEG.sum())


def Finv(G):
    return np.fft.ifft(G) / DU


def family(width, cell):
    """Unit-norm indicator pixels of width `cell` tiling [-width, 0]."""
    ncell = int(round(width / cell))
    fam = []
    for i in range(ncell):
        lo = -width + i * cell
        idx = np.where((X >= lo - 0.25 * DU) & (X < lo + cell - 0.25 * DU))[0]
        h = np.zeros(N, dtype=complex)
        h[idx] = 1.0 / np.sqrt(cell)
        fam.append(h)
    return fam


def sigma_min(fam, symbol, shift_samples):
    """sqrt(min eig of the defect Gram matrix); pixels are unit-norm/disjoint."""
    n = len(fam)
    G = np.empty((n, NPIX), dtype=complex)
    for i, h in enumerate(fam):
        u = Finv(symbol * (np.fft.fft(h) * DU))     # c = 0 member
        G[i, :] = np.roll(u, shift_samples)[NEG]    # exact shift by +|c|
    A = (G.conj() @ G.T) * DU
    A = 0.5 * (A + A.conj().T)
    ev = np.linalg.eigvalsh(A)
    return float(np.sqrt(max(ev[0], 0.0)))


def main():
    m_minus = np.conj(m_of_real(XI))
    ones = np.ones_like(XI)
    famA = family(8.0, 1.0 / 16.0)
    famB = family(48.0, 1.0 / 8.0)
    print("rig: N = %d, du = %g, xi |<= %g, x |<= %g"
          % (N, DU, 1.0 / (2 * DU), N * DU / 2.0))
    print("families: A = %d cells of 1/16 on [-8,0]; B = %d cells of 1/8 on [-48,0]"
          % (len(famA), len(famB)))
    print()

    sA1 = sigma_min(famA, ones, 0)
    sAe = sigma_min(famA, ones, int(round(2.0 / DU)))      # |c| = 2, lambda = e^-1
    sB1 = sigma_min(famB, ones, 0)
    sBe = sigma_min(famB, ones, int(round(2.0 / DU)))
    print("calibrations (model m := 1):")
    print("    lambda = 1    : A %.6e  B %.6e   (exact 1.0)" % (sA1, sB1))
    print("    lambda = e^-1 : A %.6e  B %.6e   (exact 0.0)" % (sAe, sBe))
    print()

    # lambda grid: |c| = j * du, j = 0, 8, 16, ..., 256  ->  |c| in [0, 2]
    js = [0, 8, 16, 24, 32, 48, 64, 96, 128, 160, 192, 256, 320, 384]
    print("real symbol m (m(-xi) = conj(m)); |c| = 2|log l| in [0, 3]")
    print("+------+----------+----------------+----------------+--------+--------+")
    print("| j/du |  lambda  | sigma_min(A)   | sigma_min(B)   |  p_A   |  p_B   |")
    print("+------+----------+----------------+----------------+--------+--------+")
    prev = None
    for j in js:
        lam = float(np.exp(-0.5 * j * DU))
        sA = sigma_min(famA, m_minus, j)
        sB = sigma_min(famB, m_minus, j)
        pA = pB = float("nan")
        if prev is not None:
            l0, a0, b0 = prev
            if sA > 0 and a0 > 0:
                pA = np.log(sA / a0) / np.log(lam / l0)
            if sB > 0 and b0 > 0:
                pB = np.log(sB / b0) / np.log(lam / l0)
        prev = (lam, sA, sB)
        print("| %4.2f |  %7.5f |  %12.6e  |  %12.6e  | %+6.2f | %+6.2f |"
              % (j * DU, lam, sA, sB, pA, pB))
    print("+------+----------+----------------+----------------+--------+--------+")
    print()
    print("p = local log-log slope d log sigma_min / d log lambda; a stable p")
    print("means a power law sigma_min ~ lambda^p, a drifting p means the true")
    print("law is not a pure power (compare against exp(-a|c|) and exp(-a|c|^2)).")


if __name__ == "__main__":
    main()