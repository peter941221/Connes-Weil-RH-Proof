#!/usr/bin/env python3
"""Fast numeric evaluator for the tree's Gamma_R symbol (record 1630).

Committed symbol (1626 sec 2, 1630 sec 2):

    m(xi) = Gamma_R(1/2 - 2 pi i xi) / Gamma_R(1/2 + 2 pi i xi)
          = e^{2 pi i xi log pi} Gamma(1/4 - pi i xi) / Gamma(1/4 + pi i xi),

and on the real axis the Schwarz reflection Gamma(conj z) = conj(Gamma(z))
collapses the ratio to a unit-modulus phase,

    m(xi) = exp( 2 pi i xi log pi - 2 i Im logGamma(1/4 + pi i xi) ),   |m| = 1,

with  m(-xi) = conj(m(xi)) = 1/m(xi).

Off the real axis (B4-scalar slice test) the full ratio is needed:
z = x + I y,  m(z) = exp( 2 pi i z log pi + logG(1/4 - pi i z) - logG(1/4 + pi i z) ).

Evaluation strategy: vectorized Stirling asymptotic with 14 Bernoulli terms for
|z| >= 8 (error ~ 1e-21 there), mpmath loggamma for the disc |z| < 8 (a few
thousand points per slice, negligible cost).  Run as a script for a self-test
against mpmath at 25 digits.

Why not mpmath everywhere: the B4 rig needs ~2e6 x 9 evaluations of the symbol;
mpmath at that volume runs for tens of minutes (observed), the vectorized
version for seconds.  The Stirling series and the mpmath fallback are checked
against each other in the self-test below, so the speedup costs no accuracy.
"""

import numpy as np
import mpmath as mp

# c_k = B_{2k} / (2k (2k-1)) for the logGamma asymptotic
_STIRLING = np.array([
    1.0 / 12.0,
    -1.0 / 360.0,
    1.0 / 1260.0,
    -1.0 / 1680.0,
    1.0 / 1188.0,
    -691.0 / 360360.0,
    1.0 / 156.0,
    -3617.0 / 122400.0,
    43867.0 / 244188.0,
    -174611.0 / 125400.0,
    854513.0 / 63756.0,
    -236364091.0 / 1506960.0,
    8553103.0 / 4212.0,
    -23749461029.0 / 756900.0,
])

LOG_PI = float(np.log(np.pi))
_HALF_LOG_2PI = 0.5 * float(np.log(2.0 * np.pi))
_STIRLING_MIN = 8.0


def loggamma_stirling(z):
    """log Gamma(z) by the Stirling asymptotic; z: complex ndarray, |z| >= 8."""
    z = np.asarray(z, dtype=complex)
    acc = np.zeros_like(z)
    power = 1.0 / z
    zsq = z * z
    for c in _STIRLING:
        acc = acc + c * power
        power = power / zsq
    return (z - 0.5) * np.log(z) - z + _HALF_LOG_2PI + acc


def _loggamma_mp(z, dps=18):
    """mpmath loggamma at a single complex point (small-|z| fallback)."""
    old = mp.mp.dps
    mp.mp.dps = dps
    val = mp.loggamma(mp.mpc(z.real, z.imag))
    mp.mp.dps = old
    return complex(val)


def _fill_small(z, out, dps=18):
    """Replace entries of `out` by mpmath values where |z| < _STIRLING_MIN."""
    small = np.abs(z) < _STIRLING_MIN
    if not small.any():
        return out
    for idx in np.argwhere(small):
        i = tuple(idx)
        out[i] = _loggamma_mp(complex(z[i]), dps=dps)
    return out


def m_of(z):
    """m(z) at complex points z (vectorized, with the small-|z| patch)."""
    z = np.asarray(z, dtype=complex)
    u = 0.25 - 1j * np.pi * z
    v = 0.25 + 1j * np.pi * z
    lu = loggamma_stirling(u)
    lv = loggamma_stirling(v)
    _fill_small(u, lu)
    _fill_small(v, lv)
    return np.exp(2j * np.pi * z * LOG_PI + lu - lv)


def m_of_real(xi):
    """m on the real axis, unit modulus (vectorized)."""
    xi = np.asarray(xi, dtype=float)
    z = 0.25 + 1j * np.pi * xi
    lg = loggamma_stirling(z)
    _fill_small(z, lg)
    return np.exp(2j * np.pi * xi * LOG_PI - 2j * np.imag(lg))


def inv_m_of_real(xi):
    """1/m = conj(m) on the real axis."""
    return np.conj(m_of_real(xi))


def _self_test():
    mp.mp.dps = 25
    pts = [0.0, 0.5, 1.0, 3.0, 7.9, 8.1, 20.0, 137.0, 500.0]
    print("self-test  m(xi) vs mpmath (25 digits)")
    print("     xi            |m|            phase error        value error")
    worst = 0.0
    for xi in pts:
        z = complex(0.25 + 1j * np.pi * xi)
        ref = complex(mp.e ** (2j * mp.pi * xi * mp.log(mp.pi))
                      * mp.gamma(0.25 - 1j * mp.pi * xi)
                      / mp.gamma(0.25 + 1j * mp.pi * xi))
        got = complex(m_of_real(np.array([xi]))[0])
        err = abs(got - ref)
        worst = max(worst, err)
        print("  %8.4f   %14.12f   %14.4e   %14.4e"
              % (xi, abs(got), abs(got / ref - 1.0), err))
    # off-axis: the full ratio at a genuinely complex point
    for y in [0.05, 0.0795775, 0.3]:
        z = complex(1.3 + 1j * y)
        ref = complex(mp.e ** (2j * mp.pi * z * mp.log(mp.pi))
                      * mp.gamma(0.25 - 1j * mp.pi * z)
                      / mp.gamma(0.25 + 1j * mp.pi * z))
        got = complex(m_of(np.array([z]))[0])
        worst = max(worst, abs(got - ref))
        print("  z = 1.3 + %8.6f I : value error %14.4e" % (y, abs(got - ref)))
    print("  worst absolute error: %14.4e" % worst)
    # the identities quoted in the docstring
    xi = np.array([0.3, 2.0, 11.0, 40.0])
    lhs = m_of_real(-xi)
    rhs = 1.0 / m_of_real(xi)
    print("  max |m(-xi) - 1/m(xi)| on a sample: %14.4e" % np.max(np.abs(lhs - rhs)))
    print("  max ||m(xi)| - 1| on a sample:      %14.4e"
          % np.max(np.abs(np.abs(m_of_real(xi)) - 1.0)))


if __name__ == "__main__":
    _self_test()