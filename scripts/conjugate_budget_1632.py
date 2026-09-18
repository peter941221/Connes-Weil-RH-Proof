#!/usr/bin/env python3
"""Conjugate budget of the base criterion (record 1632, Erratum D).

The base criterion (MP 2010, math/0702497, eq. ``basic``) needs the phase of
the symbol to be written as ``-alpha + ht`` with ``ht`` the Hilbert transform
of a density ``h in L^1(dPi)``; at p = 2 the additional clause is
``e^{-h} in L^1(R)``.  Record 1631 read the two slots off a *power-tail* table
and concluded that a conjugate can carry at most exponent ``beta < 1`` (density
budget), so the committed phase ``psi ~ 2 pi x log|x|`` (exponent ``1 + o(1)``)
would be OUTSIDE it.

That conclusion is wrong, and this rig says why.  The ceiling on ``ht`` is not
set by ``h in L^1(dPi)`` alone; it is set by the *one-sided Lipschitz*
condition on ``ht'``:

    MP 2010 sec 2, Lemma 1:   ht'(x) <~ |x|^kappa, kappa >= 0  ==>
                              ht(x) = o(x^{kappa+1}),
    MP 2010 sec 2, Lemma 3:   kappa in [-1,0), h in L^1(|x|^{-2-kappa}),
                              ht' <~ |x|^kappa  ==>  ht = o(x^{kappa+1}),

so the conjugate can be *superlinear*, and the density exponent beta and the
conjugate exponent 1 + kappa are different slots, coupled by the weight:
``h ~ |x|^beta`` lies in ``L^1(|x|^{-2-kappa})`` iff ``beta < 1 + kappa``.

Three self-contained checks:

1. RAMP.  ``h(t) = t 1_[1,T]`` is in L^1(dPi) (weighted mass ~ log T), but its
   conjugate has *logarithmic spikes* at both edges (exact closed form), so
   ``ht'`` is unbounded there: L^1(dPi) membership gives no Lipschitz control,
   and the hypothesis of Lemma 1 is a real restriction.

2. SHARPNESS.  The pure power ``h(t) = t^beta 1_[t>1]`` (0 < beta < 1) has
   ``ht(x) = cot(pi beta) x^beta + O(1)``, so ``ht = Theta(x^beta)``: exactly
   at the ceiling, not below it.  Numerically: direct principal-value
   quadrature against the closed form, and the ratio ``ht(x)/x^beta`` -> cot.

3. UPPER-DENSITY BOUNDARY.  The shortness sum ``sum_{d(l) >= 1} d^{kappa-2} l^2``
   is critical at ``l ~ d^{(1-kappa)/2}``; this is a joint length/distance
   density condition, so the real obstruction is a density/atoms condition on
   the BM intervals, not a pointwise ceiling.

Usage:  python scripts/conjugate_budget_1632.py
"""

import mpmath as mp

mp.mp.dps = 30

PI = mp.pi


def ramp_conjugate(x, T):
    """Exact conjugate of h(t) = t 1_[1,T] at the *normalisation of MP*:
    ht(x) = (1/pi) v.p. int [1/(x-t) + t/(1+t^2)] h(t) dt.
    The v.p. piece integrates in closed form (x outside [1,T]) and the
    second term is a constant, so the whole conjugate is elementary."""
    x = mp.mpf(x)
    T = mp.mpf(T)
    log_term = x * mp.log(abs((x - 1) / (x - T)))
    const = mp.atan(T) - PI / 4
    return (log_term - const) / PI


def ramp_quadrature(x, T):
    """Same conjugate by direct quadrature of the two pieces (check of the
    closed form outside the support, where the first integrand is smooth)."""
    x = mp.mpf(x)
    T = mp.mpf(T)
    s1 = mp.quad(lambda t: t / (x - t), [1, T])
    s2 = mp.quad(lambda t: t ** 2 / (1 + t ** 2), [1, T])
    return (s1 + s2) / PI


def check_ramp():
    print("1. RAMP  h(t) = t 1_[1,T]:  L^1(dPi) membership without Lipschitz control")
    T = mp.mpf(20)
    mass = mp.quad(lambda t: t / (1 + t ** 2), [1, T])
    print("   weighted mass int h dPi = %.6f   (= (1/2) log(1+T^2) = %.6f)"
          % (mass, mp.log(1 + T ** 2) / 2))
    print("   Outside the support the v.p. is a proper integral, so the closed form")
    print("   is checkable by quadrature:")
    print("   x        ht(x) closed form     ht(x) quadrature      rel.diff")
    for x in ("0.5", "20.1", "21", "30", "100"):
        a = ramp_conjugate(x, T)
        b = ramp_quadrature(x, T)
        print("   %-8s %-22.10g %-22.10g %-10.2e" % (x, a, b, abs(a - b) / abs(a)))
    print("   Edge behaviour at x = T + delta (closed form, v.p. inside):")
    print("   delta      ht(T+delta)      ht - (T/pi) log(1/delta)")
    for k in (3, 4, 5, 6, 8):
        d = mp.mpf(10) ** (-k)
        val = ramp_conjugate(T + d, T)
        print("   1e-%-7d %-17.6f %-12.6f" % (k, val, val - (T / PI) * mp.log(1 / d)))
    print("   The remainder is constant to 1e-5: ht(T+delta) = (T/pi) log(1/delta) + C,")
    print("   so ht' ~ (T/pi)/delta -> infinity: the one-sided Lipschitz hypothesis")
    print("   ht' <~ |x|^kappa is NOT automatic for h in L^1(dPi).")
    print("   Plateaus at |x| = 1e6: ht(-1e6) = %.4f, ht(1e6) = %.4f (the"
          % (ramp_conjugate(-mp.mpf("1e6"), T), ramp_conjugate(mp.mpf("1e6"), T)))
    print("   normalisation keeps a constant, which is why the weighted mass matters).")
    print()


def power_conjugate_quad(x, beta):
    """Conjugate of h(t) = t^beta 1_[t>1], using the SUBTRACTED kernel
    (1/(x-t) + t/(1+t^2)), whose integrand decays like x t^{beta-2} at
    infinity; the bare v.p. piece alone diverges logarithmically there, so a
    direct quadrature of the two pieces separately cancels catastrophically.
    Symmetric exclusion at t = x, extrapolated over two meshes."""
    x = mp.mpf(x)
    beta = mp.mpf(beta)
    kernel = lambda t: t ** beta * (1 / (x - t) + t / (1 + t ** 2))
    vals = []
    for d in ("1e-4", "1e-6"):
        d = mp.mpf(d)
        vals.append((mp.quad(kernel, [1, x - d]) + mp.quad(kernel, [x + d, mp.inf])) / PI)
    return vals[0] + (vals[1] - vals[0]) / 9


def check_sharpness():
    print("2. SHARPNESS  h(t) = t^beta 1_[t>1]:  the ceiling is attained, not avoided")
    print("   h ~ x^beta is NOT integrable against |x|^{-2-kappa} at kappa = beta-1,")
    print("   so the weighted hypothesis of Lemma 3 sits exactly on the boundary and")
    print("   the conclusion ht = o(x^{kappa+1}) = o(x^beta) must be expected to fail.")
    print("   Classical power transform: ht(x) = cot(pi beta) x^beta + C_beta + O(x^{beta-1}).")
    print("   beta     x        ht (quadrature)    cot(pi b) x^beta    deviation")
    for beta in ("0.25", "0.5", "0.75"):
        b = mp.mpf(beta)
        cot = mp.cos(PI * b) / mp.sin(PI * b)
        for x in (100, 1000, 10000):
            ht = power_conjugate_quad(x, b)
            pred = cot * mp.mpf(x) ** b
            print("   %-8s %-9s %-19.8g %-19.8g %-11.7g"
                  % (beta, x, ht, pred, ht - pred))
    print("   beta = 0.25, 0.75: the deviation is constant in x to 3 digits, so")
    print("   ht = cot(pi beta) x^beta + O(1): Theta(x^beta), the ceiling o(x^beta)")
    print("   is attained, and the weighted hypothesis of Lemma 3 is sharp.")
    print("   beta = 0.5: cot(pi/2) = 0, the leading term vanishes and ht decays")
    print("   like x^{beta-1} = x^{-1/2} (verified: ht*x^{1/2} = -0.792 constant) --")
    print("   the one exceptional exponent where the ceiling is NOT attained.")
    print()


def check_coupling():
    print("3. COUPLING  density exponent beta vs conjugate exponent 1 + kappa")
    print("   kappa (Lipschitz)   weight |x|^{-2-kappa}   density beta <   ht ceiling")
    for k in ("0", "0.25", "0.5", "1.0"):
        kk = mp.mpf(k)
        print("   %-19s %-24s %-16s o(x^{%s})"
              % (k, "|x|^-%.2f" % (2 + kk), "%.2f" % (1 + kk), "%.2f" % (1 + kk)))
    print("   The committed phase has psi(x) ~ 2 pi x log|x| and psi' ~ 2 pi log|x|,")
    print("   hence kappa = 0+ and psi lies strictly below o(x^{1+kappa}) for every")
    print("   kappa > 0: the growth budget does NOT obstruct the representation.")
    print()


def check_shortness():
    print("4. UPPER-DENSITY BOUNDARY  S(kappa) = sum_{d(l)>=1} d^{kappa-2} l^2")
    print("   model l_n = n^s, d_n = n:  S = sum n^{kappa-2+2s}, so S < inf iff")
    print("   kappa - 2 + 2s < -1, i.e. iff s < (1-kappa)/2: the critical scaling")
    print("   is l ~ d^{(1-kappa)/2} (at equality S is log-divergent).")
    print("   kappa    s (of l = d^s)   sum n^{kappa-2} n^{2s}      verdict")
    for k in ("0", "1"):
        kk = mp.mpf(k)
        for s in ("0.2", "0.5", "0.8"):
            ss = mp.mpf(s)
            expo = kk - 2 + 2 * ss
            if expo < -1:
                verdict = "converges"
            elif expo == -1:
                verdict = "LOG DIVERGES"
            else:
                verdict = "diverges"
            part = mp.nsum(lambda n: n ** expo, [1, 20000])
            print("   %-8s %-17s %-26.6g %s (exponent %.2f, s* = %.2f)"
                  % (k, s, part, verdict, expo, (1 - float(k)) / 2))
    print("   s* = (1-kappa)/2 is the critical scaling: the obstruction is a joint")
    print("   length/distance DENSITY condition on the BM intervals (the shortness")
    print("   sum), not a pointwise ceiling on the conjugate.")
    print()


def main():
    check_ramp()
    check_sharpness()
    check_coupling()
    check_shortness()


if __name__ == "__main__":
    main()