#!/usr/bin/env python3
"""1633: which half-line does the carrier kernel K = F^{-1}(m(-.)) live on?

The 1630 probe and the 1633 carrier-defect diagnostic both report the defect
||P_{x<0}(U H)||/||U H|| of a single bump column.  The mechanism question is
what K = F^{-1}(m(-.)) looks like, because U H = delta_{|c|} * K * h is a
convolution and the carrier condition is exactly "supp F^{-1}(U H) in [0, inf)".

Committed ledger (1626 sec 2, 1632 law F51): m = A/B with A = Gamma_R(1/2 - 2 pi i xi),
B = A(-.);  m has zeros at +i(4n+1)/(4 pi) and poles at -i(4n+1)/(4 pi), so
xi -> m(-xi) should be holomorphic on C_- and K = F^{-1}(m(-.)) should be
supported on [0, inf).  The diagnostic's mass table contradicts that
(98.4 percent of the mass on x < 0), so this rig runs three independent
checks:

  (1) LOCALIZATION CONTROL on symbols with known x-support:
        e^{+2 pi i mu xi}  -> delta at -mu        (analytic in C_+)
        e^{-2 pi i mu xi}  -> delta at +mu        (analytic in C_-)
        1/(1+2 pi i xi)    -> e^{-x} on x > 0     (analytic in C_-)
        sinc/box           -> box transform
  (2) MASS TEST on K for both orientations m(xi) and m(-xi) = conj(m(xi)).
  (3) POINTWISE |m| LEDGER at the claimed zeros/poles z = +-i(4n+1)/(4 pi)
      using the mpmath-backed complex evaluator, at distances d = 1e-3, 1e-1.

Run: WSL, uv run --with numpy --with scipy --with mpmath python <this file>.
"""

import numpy as np
import mpmath as mp
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rh_symbol_num import m_of_real, m_of  # noqa: E402

N = 1 << 15
DU = 1.0 / 128.0
XI = np.fft.fftfreq(N, d=DU)
DXI = 1.0 / (N * DU)
X = np.fft.fftfreq(N, d=DXI)
NEG = X < 0.0
POS = X > 0.0
SAMPLE_X = [0.5, 1.0, 2.0, 4.0, 8.0, 16.0, 32.0, 64.0]


def Finv(G):
    return np.fft.ifft(G) / DU


def mass(g):
    tot = np.sum(np.abs(g) ** 2)
    return (float(np.sum(np.abs(g[NEG]) ** 2) / tot),
            float(np.sum(np.abs(g[POS]) ** 2) / tot))


def loc_row(name, G, expected):
    K = Finv(G)
    nk, pk = mass(K)
    print("  %-26s x<0 %8.4f | x>0 %8.4f   (expected: %s)"
          % (name, nk, pk, expected))


def sample_row(g, scale):
    vals = []
    for x0 in SAMPLE_X:
        i = int(round(x0 / DU)) % N
        j = (-int(round(x0 / DU))) % N
        vals.append((abs(g[i]), abs(g[j])))
    print("    sample |g| at x = +-%.1f,... (scaled by 1/%s):" % (SAMPLE_X[0], scale))
    print("      x>0: " + "  ".join("%8.2e" % (v[0] / scale) for v in vals))
    print("      x<0: " + "  ".join("%8.2e" % (v[1] / scale) for v in vals))


def main():
    print("=== (1) localization controls on the same grid and window ===")
    mu = 2.0
    loc_row("e^{+2pi i mu xi}, mu=2", np.exp(2j * np.pi * mu * XI),
            "delta at -2 (x<0)")
    loc_row("e^{-2pi i mu xi}, mu=2", np.exp(-2j * np.pi * mu * XI),
            "delta at +2 (x>0)")
    loc_row("1/(1+2 pi i xi)", 1.0 / (1.0 + 2j * np.pi * XI),
            "e^{-x} on x>0 (x>0)")
    box = (np.abs(XI) < 8.0).astype(float)          # box in xi of half-width 8
    loc_row("box(|xi|<8)", box, "sinc, even in x (both sides)")
    print()

    print("=== (2) the carrier kernel K, both orientations ===")
    m_r = m_of_real(XI)
    loc_row("K from m(-xi) = conj(m)", np.conj(m_r), "predicted x>0 (C_-)")
    loc_row("K from m(+xi)", m_r, "predicted x<0 (C_+)")
    print()
    K_minus = Finv(np.conj(m_r))
    print("    sample decay of |K| for m(-xi) (unnormalized):")
    sample_row(K_minus, 1.0)
    print()

    print("=== (3) pointwise |m| at the claimed zeros/poles ===")
    print("    z = +i(4n+1)/(4pi) (claimed ZERO of m) and its mirror (claimed POLARITY)")
    mp.mp.dps = 20
    for n in range(4):
        z = 1j * (4 * n + 1) / (4 * np.pi)
        row = []
        for d in (1e-3, 1e-1):
            v_p = complex(m_of(np.array([z + d]))[0])
            v_m = complex(m_of(np.array([z - d]))[0])
            w_p = complex(m_of(np.array([-z + d]))[0])
            w_m = complex(m_of(np.array([-z - d]))[0])
            row.append((abs(v_p), abs(v_m), abs(w_p), abs(w_m)))
        print("    n=%d  |m(z+d)|=%9.3e |m(z-d)|=%9.3e |m(-z+d)|=%9.3e |m(-z-d)|=%9.3e"
              % (n, row[0][0], row[0][1], row[0][2], row[0][3]))
        print("          d=0.1: |m(z+d)|=%9.3e |m(z-d)|=%9.3e |m(-z+d)|=%9.3e |m(-z-d)|=%9.3e"
              % (row[1][0], row[1][1], row[1][2], row[1][3]))
    print("    |m(i)| = %.6e   |m(-i)| = %.6e   (1632 ledger: 806.9)"
          % (abs(complex(m_of(np.array([1j]))[0])),
             abs(complex(m_of(np.array([-1j]))[0]))))
    print("    |m| on the real axis: max ||m|-1| = %.3e"
          % np.max(np.abs(np.abs(m_r) - 1.0)))


if __name__ == "__main__":
    main()