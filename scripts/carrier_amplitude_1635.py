#!/usr/bin/env python3
"""1635 (O1'): the amplitude profile, and the universality of c0.

Items 1 and 2 of the 1634 next-step list, in one rig.

(A) PROFILE.  Is D_real/D_model ~ 0.080 a LOCAL statement?  Compute
    v = F^{-1}(m(-.) Hhat) and h on the same grid at k = 3, lambda = 0.002 and
    print |v(y)| / |h(y - s)| for shifts s in {-1, -0.5, 0, 0.5, 1}:
    a flat ratio at s = 0 means the multiplier acts as a constant multiple of
    the identity (in modulus) on the window; a ratio peaked away from s = 0
    means a constant-amplitude FREE SHIFT by s* (the 1634 F56 picture).

(B) UNIVERSALITY + the 1/(4 pi) conjecture.  General one-pole rational family

        Hhat_a(xi) = (a - 2 pi i xi)^{-k},
        h_a(x)    = e^{a x} x^{k-1}/(k-1)! 1_{x<0},
        pole at xi = -i a/(2 pi), distance a/(2 pi) from the real axis,

    with exact model D_model^2 = Gamma(2k-1, 2 a |c|)/Gamma(2k-1).  If c0 is a
    universal NUMBER (1/(4 pi)), c0 must be independent of a.  If c0 is a
    universal FUNCTION of the pole distance d = a/(2 pi) -- which is what the
    FIO-symbol picture predicts, since the leading symbol of a chirp FIO is
    fixed by the pole -- then c0(a) scales with a.  This is the decisive split
    and it costs one field of numbers.  Superpositions h_3 + b h_2 test whether
    c0 survives mixing (F56 is about a family, not a single vector).

Run: WSL, uv run --with numpy --with scipy --with mpmath python <this file>.
"""

import numpy as np
import scipy.special as sp
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rh_symbol_num import m_of_real  # noqa: E402

NBITS = int(sys.argv[1]) if len(sys.argv) > 1 else 15
N = 1 << NBITS
DU = 1.0 / 128.0
DXI = 1.0 / (N * DU)
XI = np.fft.fftfreq(N, d=DU)
X = np.fft.fftfreq(N, d=DXI)
NEG = X < 0.0


def h_of_a(a, k):
    """h_a(x) = e^{a x} x^{k-1}/(k-1)! on x < 0."""
    h = np.zeros(N, dtype=complex)
    m = X < 0.0
    h[m] = np.exp(a * X[m]) * X[m] ** (k - 1) / float(sp.factorial(k - 1))
    return h


def v_of(h, m_minus):
    """v = F^{-1}(m(-.) Hhat).  F(h)(xi) = int h e^{-2 pi i x xi} dx."""
    hhat = np.fft.fft(h) * DU
    return np.fft.ifft(m_minus * hhat) / DU


def half_mass(v, c):
    """mass of v on (-inf, c), c < 0, relative to ||v||^2."""
    return float(np.linalg.norm(v[X < c]) ** 2 / np.linalg.norm(v) ** 2)


def d_model(a, k, c_abs):
    return float(np.sqrt(sp.gammaincc(2 * k - 1, 2 * a * c_abs)))


def main():
    m_minus = np.conj(m_of_real(XI))
    print("rig: N = %d, |xi| <= %g, |x| <= %g, dx = %g"
          % (N, 1 / (2 * DU), N * DU / 2, DXI))
    print()

    # ---------------- (A) profile ----------------
    k, a, lam = 3, 1.0, 0.002
    c = 2.0 * np.log(lam)
    h = h_of_a(a, k)
    v = v_of(h, m_minus)
    print("=== A. profile |v(y)| vs |h(y)|, k = %d, a = %g, lambda = %g (c = %.3f) ==="
          % (k, a, lam, c))
    print("v = F^{-1}(m(-.) Hhat);  h = the model output.")
    print("+---------+--------------+--------------+----------+----------+----------+")
    print("|   y     |   |h(y)|     |   |v(y)|     | r(s=-1)  | r(s=0)   | r(s=0.5)|")
    print("+---------+--------------+--------------+----------+----------+----------+")
    xm = np.log(np.abs(X) + 1e-300)  # placeholder to keep flake quiet
    del xm
    for y in (-4.0, -6.0, -8.0, -10.0, -12.0, -14.0, -16.0):
        i = int(round(y / DXI)) % N
        hm = abs(h[i])
        vm = abs(v[i])
        out = []
        for s in (-1.0, 0.0, 0.5):
            j = int(round((y - s) / DXI)) % N
            out.append(abs(h[j]))
        print("| %7.2f | %12.4e | %12.4e | %8.4f | %8.4f | %8.4f |"
              % (y, hm, vm, vm / out[0], vm / out[1], vm / out[2]))
    print("+---------+--------------+--------------+----------+----------+----------+")
    print("if a column is flat, that shift is the one; r = |v|/|h(.-s)|.")
    print()

    # ---------------- (B) universality ----------------
    print("=== B. universality of c0 in the pole distance d = a/(2 pi) ===")
    print("ratio = D_real / D_model at |c| = 2|log lambda|; same translated vector")
    print("s = 0 is the stable primary readback; rightward translates are diagnostic only.")
    print("+------+-------+---------+---------+--------------+--------------+----------+----------+")
    print("|  k   |   a   |  d=g   | lambda  |  D_model(s0) |  D_real(s0)  | ratio_s0 | family/s0 |")
    print("+------+-------+---------+---------+--------------+--------------+----------+----------+")
    for k in (2, 3):
        for a in (0.5, 1.0, 2.0):
            h0 = h_of_a(a, k)
            for lam in (0.02, 0.01, 0.005, 0.002, 0.001, 0.0005):
                c = 2.0 * np.log(lam)
                c_abs = -c
                U = np.exp(2j * np.pi * c * XI)
                bm = br = np.inf
                dm0 = dr0 = float("nan")
                for s in (0, 1, 2, 3, 4, 6, 8):
                    h = np.roll(h0, int(round(s / DU)))
                    dm = np.sqrt(half_mass(h, c))
                    dr = np.sqrt(half_mass(v_of(h, m_minus), c))
                    if s == 0:
                        dm0, dr0 = dm, dr
                    bm = min(bm, dm)
                    br = min(br, dr)
                print("|  %d   | %5.2f | %7.4f | %7.4f | %12.4e | %12.4e | %8.4f | %8.4f |"
                      % (k, a, a / (2 * np.pi), lam, dm0, dr0, dr0 / dm0, br / bm))
    print("+------+-------+---------+---------+--------------+--------------+----------+----------+")
    print("exact check: D_model(a,k,c) = sqrt(Gamma(2k-1, 2 a |c|)/Gamma(2k-1))")
    for k in (2, 3):
        for a in (0.5, 1.0, 2.0):
            h0 = h_of_a(a, k)
            for lam in (0.002,):
                c = 2.0 * np.log(lam)
                h = h0
                bm = np.sqrt(half_mass(h, c))
                ex = d_model(a, k, -c)
                print("    k=%d a=%g lam=%g : measured min %.6e   exact %.6e   rel %.2e"
                      % (k, a, lam, bm, ex, abs(bm - ex) / ex))

    # ---------------- (C) superposition ----------------
    print()
    print("=== C. superposition h = h_3 + b h_2 (a = 1), lambda = 0.002 ===")
    print("+----------+--------------+--------------+----------+")
    print("|    b     |  D_model     |  D_real      | ratio    |")
    print("+----------+--------------+--------------+----------+")
    h3 = h_of_a(1.0, 3)
    h2 = h_of_a(1.0, 2)
    for b in (0.0, 0.1, 1.0, 10.0):
        h0 = h3 + b * h2
        lam = 0.002
        c = 2.0 * np.log(lam)
        h = h0
        bm = np.sqrt(half_mass(h, c))
        br = np.sqrt(half_mass(v_of(h, m_minus), c))
        print("| %8.2f | %12.4e | %12.4e | %8.4f |" % (b, bm, br, br / bm))
    print("+----------+--------------+--------------+----------+")


if __name__ == "__main__":
    main()
