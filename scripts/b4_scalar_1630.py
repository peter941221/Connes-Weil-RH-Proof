#!/usr/bin/env python3
"""1630 numeric, map 043 item 2: write psi = F^{-1} v for explicit columns and
test the committed B4-scalar premise by its definition.

Committed content (1628 sec 3, quoted verbatim):

  (B4-scalar)   xi |-> e^{2 pi I (log lambda'') xi} * m(xi) * psi(xi)  in  H^2(C_+),
                psi := F^{-1} v for the committed column v,

and, on the same page, the committed growth caveat

  "|m| ~ |x|^{2 pi y} is not uniformly polynomial in C_+".

This rig does three things, all self-contained:

 (1) the committed growth caveat, measured:  |m(x + I y)| / |x|^{2 pi y}  along
     the slice, for several y (B4-scalar needs the product to be L^2 on every
     slice with a bound uniform in y, so the |m|-growth is the load-bearing
     term);
 (2) the slice norms  G(y, X) = (INT_{-X}^{X} |Psi(x + I y)|^2 dx)^{1/2}  of
     Psi(xi) = e^{2 pi I C xi} m(xi) psi(xi),  C = log lambda'' = log(1/2),
     for psi = F^{-1} v of three explicit columns v;  convergence in X at fixed
     y is the numeric signature of dxi-finiteness on that slice, growth in X
     its failure, and the growth of the converged norms in y is what decides
     H^2(C_+);
 (3) the tap identity of 1630 sec 8:  INT_R w = Gamma_R(1/2)/2,  w(u) =
     e^{u/2} e^{-pi e^{2u}}.

Convention: F(v)(xi) = INT v(s) e^{-2 pi I s xi} ds, so F^{-1}(v)(xi) =
INT v(s) e^{2 pi I s xi} ds and a column supported on [a, b] gives
psi(xi) = INT_a^b v(s) e^{2 pi I s xi} ds - analytic in C_+ with the growth
e^{2 pi b y} (compact support) or e^{-2 pi a y} (half-line with decay).
The product Psi is analytic in C_+ wherever psi is (m is analytic in C_+, its
poles sit in C_-).

Run: WSL, numpy (+ scripts/rh_symbol_num).  Deterministic.
"""

import numpy as np
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rh_symbol_num import m_of, m_of_real  # noqa: E402

NBITS = 20
N = 1 << NBITS
L = 1024.0                       # spatial period
DU = L / N                       # spatial step
DXI = 1.0 / L                    # xi step
XI = np.fft.fftfreq(N, d=DU)     # xi grid: |xi| <= 1/(2 DU) = 512
C_LAMBDA = float(np.log(0.5))    # log lambda''  (lambda'' = 1/2)

YS = [0.005, 0.02, 0.05, 0.079, 0.0795775, 0.08, 0.1, 0.3, 1.0]
XS = [20.0, 100.0, 500.0]
THRESHOLD = 1.0 / (4.0 * np.pi)  # 0.0795775


def psi_window(xi):
    """F^{-1} of 1_[0,1]:  (e^{2 pi I xi} - 1) / (2 pi I xi)."""
    out = np.empty_like(xi)
    small = np.abs(xi) < 1e-12
    out[small] = 1.0
    z = xi[~small]
    out[~small] = (np.exp(2j * np.pi * z) - 1.0) / (2j * np.pi * z)
    return out


def psi_exp(xi):
    """F^{-1} of e^{-s/2} 1_[0, inf):  1 / (1/2 - 2 pi I xi)."""
    return 1.0 / (0.5 - 2j * np.pi * xi)


def psi_bump(xi, y):
    """F^{-1} of the C^inf bump on [0,1], on the slice xi = x + I y.

    psi(x + I y) = INT h(s) e^{2 pi I s (x + I y)} ds = FFT of h(s) e^{2 pi y s}
    on the dual grid (period L, step DU), one transform per slice.
    """
    s = -L / 2.0 + np.arange(N) * DU
    h = np.zeros_like(s)
    inside = (s > 0.0) & (s < 1.0)
    t = 2.0 * (s[inside] - 0.5)
    h[inside] = np.exp(1.0 - 1.0 / (1.0 - t * t))
    weighted = np.zeros_like(h)
    weighted[inside] = h[inside] * np.exp(2.0 * np.pi * y * s[inside])
    return np.fft.fft(np.fft.fftshift(weighted)) * DU


def slice_norms(Psi):
    """G(y, X) for the partial sums on one slice."""
    out = []
    for X in XS:
        sel = np.abs(XI) <= X
        out.append(float(np.sqrt(DXI * np.sum(np.abs(Psi[sel]) ** 2))))
    return out


def main():
    print("B4-scalar probe:  Psi(xi) = e^{2 pi I C xi} m(xi) psi(xi),  C = log(1/2)")
    print("grid: N = %d, period %s, dxi = %s, |xi| <= %s"
          % (N, L, DXI, XI.max()))
    print("strip threshold 1/(4 pi) = %.10f" % THRESHOLD)
    print()

    # (3) the tap identity of 1630 sec 8
    # left end must reach well past the u^{1/2} tail: INT_{-inf}^{-40} e^{u/2} du
    # = 2 e^{-20} = 4e-9, while at u = -6 the tail is still 2 e^{-3} = 0.0996.
    u = np.linspace(-40.0, 4.0, 1 << 21)
    w = np.exp(u / 2.0) * np.exp(-np.pi * np.exp(2.0 * u))
    tap = float(np.trapezoid(w, u))
    from mpmath import mp, gamma, pi as mpi
    mp.dps = 25
    a0 = float(mpi ** mp.mpf(-0.25) * gamma(mp.mpf(1) / 4))
    print("tap identity:  INT_R w = %.10f,  Gamma_R(1/2)/2 = %.10f  (diff %.3e)"
          % (tap, a0 / 2.0, abs(tap - a0 / 2.0)))
    print()

    # (1) the committed growth caveat
    print("(1) committed growth caveat:  |m(x + I y)| / |x|^{2 pi y} on the slice")
    print("      y        x = 20        x = 100       x = 500     log10|m| at x=500")
    for y in YS:
        row = []
        for x in (20.0, 100.0, 500.0):
            val = complex(m_of(np.array([complex(x) + 1j * y]))[0])
            row.append(abs(val) / x ** (2.0 * np.pi * y))
        mm = complex(m_of(np.array([complex(500.0) + 1j * y]))[0])
        print("   %9.7f  %12.6e  %12.6e  %12.6e   %10.4f"
              % (y, row[0], row[1], row[2], np.log10(abs(mm))))
    print()

    # (2) the slice norms per column
    columns = [
        ("v = 1_[0,1]                (compact window)", psi_window),
        ("v = C^inf bump on [0,1]    (compact, smooth)", None),
        ("v = e^{-s/2} 1_[0,inf)     (half-line, decay)", psi_exp),
    ]
    for name, maker in columns:
        print("column: %s" % name)
        print("      y        G(X=20)        G(X=100)       G(X=500)    G500/G20")
        for y in YS:
            xi = XI.astype(complex) + 1j * y
            A = np.exp(2j * np.pi * C_LAMBDA * xi) * m_of(xi)
            psi = maker(xi) if maker is not None else psi_bump(xi, y)
            Psi = A * psi
            g = slice_norms(Psi)
            print("   %9.7f  %12.6e  %12.6e  %12.6e   %9.4f"
                  % (y, g[0], g[1], g[2], g[2] / g[0]))
        print()
    print("notes:")
    print("  - G500/G20 -> 1  : slice in L^2(R);  growth in X: slice not in L^2(R)")
    print("  - H^2(C_+) needs every slice in L^2(R) AND the slice norms bounded")
    print("    uniformly in y;  the |m| ~ |x|^{2 pi y} growth of part (1) is what")
    print("    makes the two requirements collide at y ~ 1/(4 pi) for psi ~ 1/|x|.")
    print("  - psi = m(xi) itself is NOT used anywhere: the rig tests the committed")
    print("    product, not a re-derivation; m on the real axis is checked in the")
    print("    self-test of scripts/rh_symbol_num.py.")


if __name__ == "__main__":
    main()