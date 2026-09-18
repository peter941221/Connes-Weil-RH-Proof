#!/usr/bin/env python3
"""1633 diagnostic: where does F^{-1}(U H) live, and how big is its wrong-half mass?

Committed base (1629 sec 3, 1629 sec 4 correction; probe form of 1630 sec 2):

    carrier(l) != {0}   <=>   exists H in H^2(C_+) \\ {0}  with  U . H in H^2(C_-),
    U(xi) = e^{2 pi i c xi} m(-xi),   c = 2 log l <= 0.

Dictionary, fixed once and used everywhere below (x = transform variable,
F(h)(xi) = INT h(x) e^{-2 pi i x xi} dx, so F^{-1}(g)(x) = INT g(xi) e^{2 pi i x xi} dxi):

    H^2(C_+) = analytic in the upper half plane = { F h : supp h in (-inf, 0] },
    H^2(C_-) = analytic in the lower half plane = { F h : supp h in [0, inf) }.

The two structural facts this rig tests numerically:

  (i)  K := F^{-1}(m(-.)) is supported in [0, inf), because xi -> m(-xi) is
       holomorphic on C_- (its poles sit at +i(4n+1)/(4 pi) in C_+);
  (ii) consequently (delta_{|c|} * K * h)(x) is supported in [|c| - W, inf)
       for h of support width W, so for |c| >= W the function U H would sit
       EXACTLY on [0, inf) -- an exact finite-type witness.  The 1630 probe
       reports sigma_min > 0 for the real m at |c| >= 1, so at least one of
       (i)/(ii), the dictionary, or the committed form must fail; this rig
       locates the failure by direct inspection of the x-profiles.

Output: for each case, the mass fractions of F^{-1}(H), F^{-1}(U H) and K on
x < 0 / x > 0, plus coarse x-profiles.  Calibrations: model m = 1, l = e^{-1}
(exact witness: h(.-2) sits on [1,2]) and model m = 1, l = 1 (U = 1, no
witness).  Run: WSL, uv run --with numpy --with scipy --with mpmath python.
"""

import numpy as np
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rh_symbol_num import m_of_real  # noqa: E402

N = 1 << 15
DU = 1.0 / 128.0
U_W = N * DU / 2.0
XI = np.fft.fftfreq(N, d=DU)            # xi-grid, spacing 1/(N DU)
DXI = 1.0 / (N * DU)
X = np.fft.fftfreq(N, d=DXI)            # x-grid, spacing DU, extent +-U_W


def F(h):
    """Fourier transform: x-grid array -> xi-grid array (fft order both)."""
    return np.fft.fft(h) * DU


def Finv(G):
    """Inverse Fourier transform: xi-grid array -> x-grid array."""
    return np.fft.ifft(G) / DU


def bump(x):
    """C^inf bump supported on [-1, 0] (same shape as the 1630 probe)."""
    out = np.zeros_like(x)
    inside = (x > -1.0) & (x < 0.0)
    s = 2.0 * (x[inside] + 0.5)
    out[inside] = np.exp(1.0 - 1.0 / (1.0 - s * s))
    return out


NEG = X < 0.0
POS = X > 0.0


def mass(g):
    """(fraction of L2 mass on x<0, fraction on x>0)."""
    tot = np.sum(np.abs(g) ** 2)
    return (np.sum(np.abs(g[NEG]) ** 2) / tot, np.sum(np.abs(g[POS]) ** 2) / tot)


def profile(g, label, half=12.0):
    """Coarse |g| profile on [-half, half], 24 cells."""
    print("    |%s| profile (24 cells over [-%.0f, %.0f]):" % (label, half, half))
    edges = np.linspace(-half, half, 25)
    cells = []
    for a, b in zip(edges[:-1], edges[1:]):
        m = (X >= a) & (X < b)
        cells.append(np.sqrt(np.mean(np.abs(g[m]) ** 2)) if m.any() else 0.0)
    scale = max(cells) if max(cells) > 0 else 1.0
    for i in range(0, 24, 8):
        row = "      x in [%6.1f,%6.1f]: " % (edges[i], edges[i + 8])
        row += "  ".join("%8.2e" % (c / scale) for c in cells[i:i + 8])
        print(row + "   (normalized to the max cell)")


def run(name, lam, model, h, m_minus):
    c = 2.0 * float(np.log(lam))
    H0 = F(h)
    U = np.exp(2j * np.pi * c * XI) * (1.0 if model else m_minus)
    G = U * H0
    g = Finv(G)
    n0, p0 = mass(Finv(H0))
    ng, pg = mass(g)
    print("%s   (lambda = %g, c = 2 log lambda = %+.4f)" % (name, lam, c))
    print("    ||P_{x<0} H||/||H|| = %.6e    (H must be in H^2(C_+): expect ~0)"
          % np.sqrt(n0))
    print("    ||P_{x<0} U H||/||U H|| = %.6e    (0 = exact witness, 1 = none)"
          % np.sqrt(ng))
    print("    mass(UH): x<0 %.4f | x>0 %.4f" % (ng, pg))
    profile(g, "F^{-1}(U H)", half=12.0)
    print()
    return float(np.sqrt(ng))


def main():
    x = X
    h = bump(x)
    m_minus = np.conj(m_of_real(XI))
    print("carrier-defect diagnostic, N = %d, du = %g, xi in [%g, %g)"
          % (N, DU, -1.0 / (2 * DU), 1.0 / (2 * DU)))
    print("x-grid: [%g, %g), spacing %g;  ||h|| = %.6f, supp h = [-1, 0]"
          % (-U_W, U_W, DU, np.linalg.norm(h)))
    print()

    # --- the kernel K = F^{-1}(m(-.)): fact (i) under test -------------------
    K = Finv(m_minus)
    nk, pk = mass(K)
    print("K = F^{-1}(m(-.)) on the sampled xi-window:")
    print("    mass(K): x<0 %.6f | x>0 %.6f   (fact (i) predicts x<0 ~ 0)"
          % (nk, pk))
    profile(K, "K", half=12.0)
    print()

    # --- calibrations and the real symbol ------------------------------------
    d_model_e1 = run("model m = 1, lambda = 1/e ", 1.0 / np.e, True, h, m_minus)
    d_model_1 = run("model m = 1, lambda = 1   ", 1.0, True, h, m_minus)
    d_real_1 = run("real  m,     lambda = 1   ", 1.0, False, h, m_minus)
    d_real_h = run("real  m,     lambda = 1/2 ", 0.5, False, h, m_minus)
    d_real_e = run("real  m,     lambda = 1/e ", 1.0 / np.e, False, h, m_minus)
    d_real_01 = run("real  m,     lambda = 0.1 ", 0.1, False, h, m_minus)

    print("cross-check against the 1630 probe D[H_0] column:")
    print("    real m, l = 1  : %.6e (probe 4.318915e-01)" % d_real_1)
    print("    real m, l = 1/2: %.6e (probe 6.900534e-02)" % d_real_h)
    print("    real m, l = 1/e: %.6e (probe 2.687186e-02)" % d_real_e)
    print("    real m, l = 0.1: %.6e (probe 3.030392e-06)" % d_real_01)
    print("    model  m = 1, l = 1/e: %.6e (probe floor 3.55e-16)" % d_model_e1)
    print("    model  m = 1, l = 1  : %.6e (probe 1.0)          " % d_model_1)


if __name__ == "__main__":
    main()