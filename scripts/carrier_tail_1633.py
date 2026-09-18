#!/usr/bin/env python3
"""1633 (map 043 item 3, stage 3): the critical-frequency tail law.

Mechanism (derived, then tested here).  Write the symbol phase on the real
axis as U(xi) = exp(2 pi i c xi) m(-xi) with c = 2 log lambda.  The committed
1631 phase budget gives m(-xi) = exp(i gamma(-xi)),
gamma(-xi) = 2 pi xi log|xi| - 2 pi xi + pi/4 + O(1/xi), so the total phase is

    psi(xi) = 2 pi [ xi log|xi| + (c-1) xi ] + pi/4 + O(1/xi).

Stationary phase for u = F^{-1}(U . Hhat) in the x-picture:

    psi'(xi) + 2 pi x = 0   =>   x = -( log|xi| + c ) = -log|xi| - 2 log lambda,

so the mass carried by frequency xi lands near x(xi) = -log|xi| - 2 log lambda,
and the half-line boundary x = 0 sits exactly at the CRITICAL FREQUENCY

    xi_c(lambda) = lambda^{-2}.

Below xi_c the mass lands on x > 0 (the good half), above xi_c on x < 0.  The
leading-order prediction is therefore

    D(lambda, H)  ~  [ mass of |Hhat|^2 on |xi| > xi_c ]^{1/2}  x  O(1),

because the wrong-half mass can only come from the part of the spectrum that
the m-chirp pushes left.  Two immediate corollaries, both already visible in
the stage-2 data:

  * a trial function with compactly supported (band-limited) Hhat below
    xi_c would be an exact witness -- but H in H^2(C_+) cannot be band-limited
    (support in x < 0 is the defining property), so the price is exactly the
    tail above xi_c, which is what the C^inf bump pays;
  * the window |xi| <= 64 makes the tail identically zero once xi_c > 64,
    i.e. lambda < 1/8, which is where the stage-2 readings collapsed to the
    rig floor.

This rig measures, for each lambda, the ratio of the measured sigma_min
(the W = 1 translate family) to sqrt(tail mass).  A stable O(1) ratio is the
confirmation.

Run: WSL, uv run --with numpy --with scipy --with mpmath python <this file>.
"""

import numpy as np
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rh_symbol_num import m_of_real  # noqa: E402
from carrier_floor_1633 import (N, DU, DXI, XI, X, NEG, bump_of_width,
                                family_shifts, span_reading)  # noqa: E402


def tail_fraction(hh, xi_c):
    """L2 mass fraction of the xi-spectrum with |xi| > xi_c."""
    p = np.abs(hh) ** 2
    tot = np.sum(p) * DXI
    return float(np.sum(p[np.abs(XI) > xi_c]) * DXI / tot)


def main():
    m_minus = np.conj(m_of_real(XI))
    hh = np.fft.fft(bump_of_width(1.0)) * DU
    shifts = family_shifts(1.0, 24.0)
    print("W = 1 family, %d translates; window |xi| <= %g" % (len(shifts), 1 / (2 * DU)))
    print()
    print("+--------+---------+------------+--------------+--------------+---------+")
    print("| lambda | xi_c    | sigma_min  | sqrt(tail)   | sigma/sqrt   | p_eff   |")
    print("+--------+---------+------------+--------------+--------------+---------+")
    prev = None
    for lam in [1.0, 0.5, 1.0 / np.e, 0.3, 0.2, 0.15, 0.125, 0.1, 0.07, 0.05, 0.03, 0.02, 0.01]:
        c = 2.0 * np.log(lam)
        xi_c = lam ** -2.0
        mod = np.exp(2j * np.pi * c * XI)
        s = span_reading(mod * m_minus, hh, shifts)
        t = np.sqrt(tail_fraction(hh, xi_c))
        ratio = s / t if t > 0 else float("nan")
        p_eff = float("nan")
        if prev is not None:
            l0, s0 = prev
            if s > 0 and s0 > 0:
                p_eff = np.log(s / s0) / np.log(lam / l0)
        prev = (lam, s)
        print("| %6.4f | %7.2f | %10.3e | %12.4e | %12.4e | %7.2f |"
              % (lam, xi_c, s, t, ratio, p_eff))
    print("+--------+---------+------------+--------------+--------------+---------+")
    print()
    print("sigma/sqrt = 1 means the defect is exactly the critical-tail amplitude.")
    print("p_eff = local slope d log sigma / d log lambda; the tail law predicts its")
    print("growth rate: d log sqrt(tail)/d log lambda.")
    print()
    prev = None
    for lam in [1.0, 0.5, 1.0 / np.e, 0.3, 0.2, 0.15, 0.125, 0.1]:
        xi_c = lam ** -2.0
        t = np.sqrt(tail_fraction(hh, xi_c))
        p = float("nan")
        if prev is not None:
            l0, t0 = prev
            if t > 0 and t0 > 0:
                p = np.log(t / t0) / np.log(lam / l0)
        prev = (lam, t)
        print("   prediction: lambda %6.4f  sqrt(tail) %.6e  slope %6.2f" % (lam, t, p))


if __name__ == "__main__":
    main()