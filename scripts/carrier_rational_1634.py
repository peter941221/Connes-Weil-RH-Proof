#!/usr/bin/env python3
"""1634 (O1): the defect as a one-sided convolution vanishing, tested on the
rational family.  Two competing laws, one decisive experiment.

Exact reformulation (pure change of variables, no approximation).

  u = F^{-1}(U_l H),  U_l(xi) = e^{2 pi i c xi} m(-xi),  c = 2 log lambda < 0.
  Put y = x + c:   u(x) = v(x + c),  v = F^{-1}(m(-.) Hhat) = K * h,  K = F^{-1}(m(-.)).
  Hence with D(H) = ||P_{x<0}(U_l H)|| / ||U_l H||,

      D^2(l, H) = INT_{-inf}^{c} |v(y)|^2 dy / INT |v(y)|^2 dy,     c = 2 log lambda,

  i.e. the carrier is nontrivial at scale l iff there is a nonzero h in
  L^2((-inf, 0]) whose convolution with K vanishes on (-inf, c).  (Model
  m := 1: K = delta and this is exactly "supp h in [c, 0]" -- the finite-type
  witness.)

Rational test family (the model floor is LIVE for it, unlike the bump family):

      Hhat_k(xi) = (1 - 2 pi i xi)^{-k},   h_k(x) = e^x x^{k-1}/(k-1)! 1_{x<0}.

  Its spectral tail above xi_c is ALGEBRAIC, so the window truncation is
  controlled (the C^inf bump's tail is super-exponential and was entirely
  eaten by the |xi| <= 64 window, which is what made the 1633 slopes
  window-limited).  Exact model answer:

      D_model^2(l, k) = Gamma(2k-1, 2|c|) / Gamma(2k-1)
                      ~ e^{-2|c|} (2|c|)^{2k-2} / Gamma(2k-1),
      D_model    ~ lambda^2 |c|^{k-1} / sqrt(Gamma(2k-1))         (position law)

  The 1633 tail law instead predicts, from the mass fraction of |Hhat|^2
  above xi_c = lambda^{-2},

      D_tail-law ~ lambda^{2k-1}      (times a k-dependent constant).

  The two agree at k = 1 (both lambda^1) and separate sharply for k >= 2:
  position law lambda^2 vs tail law lambda^3 (k = 2), lambda^5 (k = 3).
  A translate family of each h_k sharpens the bound; every number is
  reported against the exact model value of the SAME vector.

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


def h_of_k(k):
    """h_k(x) = e^x x^{k-1}/(k-1)! on x < 0, zero otherwise."""
    h = np.zeros(N, dtype=complex)
    m = X < 0.0
    h[m] = np.exp(X[m]) * X[m] ** (k - 1) / float(sp.factorial(k - 1))
    return h


def shift_by(h, s):
    """Translate h(x - s) by an integer sample count."""
    return np.roll(h, int(round(s / DU)))


def defect(U_extra, h):
    """D = ||mass on x<0 of F^{-1}(U_extra . hhat)|| / ||...||, with hhat = F(h)."""
    hhat = np.fft.fft(h) * DU
    u = np.fft.ifft(U_extra * hhat) / DU
    n = np.linalg.norm(u)
    return float(np.linalg.norm(u[NEG]) / n), u


def main():
    m_minus = np.conj(m_of_real(XI))
    print("rig: N = %d, du = %g, |xi| <= %g, |x| <= %g"
          % (N, DU, 1 / (2 * DU), N * DU / 2))
    print()

    # (0) representation check: the grid transform of h_k against the closed form
    print("representation check  max |fft(h_k)*du - (1 - 2 pi i xi)^-k| over |xi| <= 4")
    for k in (1, 2, 3, 4):
        hhat = np.fft.fft(h_of_k(k)) * DU
        ref = (1.0 - 2j * np.pi * XI) ** (-k)
        sel = np.abs(XI) <= 4.0
        print("    k = %d : %12.4e   (norm of ref %12.4e)"
              % (k, np.max(np.abs(hhat[sel] - ref[sel])), np.linalg.norm(ref[sel])))
    print()

    # (1) model floor: measured on the grid against the exact Gamma formula
    print("model floor D_model (grid) vs Gamma(2k-1, 2|c|)/Gamma(2k-1) squared")
    print("+------+---------+--------------+--------------+--------------+")
    print("|  k   |  |c|    |  measured    |  exact       |  rel. diff   |")
    print("+------+---------+--------------+--------------+--------------+")
    for k in (1, 2, 3, 4):
        for c_abs in (1.0, 4.0):
            h = h_of_k(k)
            hh = shift_by(h, -0.0)
            # model: u = h(x + c) = h(x - |c|)
            umod = np.roll(h, int(round(c_abs / DU)))
            dm = np.linalg.norm(umod[NEG]) / np.linalg.norm(umod)
            ex = np.sqrt(sp.gammaincc(2 * k - 1, 2 * c_abs))
            print("|  %d   | %5.1f   | %12.4e | %12.4e | %12.2e |"
                  % (k, c_abs, dm, ex, abs(dm - ex) / ex))
            del hh
    print("+------+---------+--------------+--------------+--------------+")
    print()

    # (2) the decisive sweep
    print("real m vs model m := 1, best over the translate family s in {0,...,-8}")
    print("p_eff = local slope d log D / d log lambda; predictions: 2k-1 (tail law),")
    print("~2 (position law).  ratio = real/model.")
    for k in (1, 2, 3, 4):
        print()
        print("=== k = %d ===" % k)
        print("+--------+---------+--------------+--------------+----------+--------+")
        print("| lambda |  |c|    |  D_model     |  D_real      | ratio    | p_eff  |")
        print("+--------+---------+--------------+--------------+----------+--------+")
        prev = None
        for lam in (1.0, 0.5, 1.0 / np.e, 0.2, 0.1, 0.05, 0.02, 0.01, 0.005):
            c = 2.0 * np.log(lam)
            U = np.exp(2j * np.pi * c * XI)
            best_m = np.inf
            best_r = np.inf
            for s in (0, -1, -2, -3, -4, -5, -6, -7, -8):
                h = shift_by(h_of_k(k), float(s))
                dm, _ = defect(U, h)
                dr, _ = defect(U * m_minus, h)
                best_m = min(best_m, dm)
                best_r = min(best_r, dr)
            p = float("nan")
            if prev is not None:
                l0, d0 = prev
                if best_r > 0 and d0 > 0:
                    p = np.log(best_r / d0) / np.log(lam / l0)
            prev = (lam, best_r)
            ratio = best_r / best_m if best_m > 0 else float("inf")
            print("| %6.4f | %7.3f | %12.4e | %12.4e | %8.4f | %6.2f |"
                  % (lam, -c, best_m, best_r, ratio, p))
        print("+--------+---------+--------------+--------------+----------+--------+")


if __name__ == "__main__":
    main()