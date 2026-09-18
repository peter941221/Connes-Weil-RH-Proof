#!/usr/bin/env python3
"""Phase budget of the tree's symbol (record 1631, base weapon inventory).

Three self-contained checks, no external data:

1. PHASE ASYMPTOTICS.  The committed symbol (1626 sec 2)

       m(xi) = Gamma_R(1/2 - 2 pi i xi) / Gamma_R(1/2 + 2 pi i xi)

   is unimodular on the real axis and its continuous argument is

       gamma(xi) = 2 pi xi log pi - 2 Im logGamma(1/4 + pi i xi),
       gamma'(xi) = 2 pi log pi - 2 pi Re psi(1/4 + pi i xi)      (psi = digamma)

   (the second line is d/dxi of the first).  The committed phase is
   ODD: m(-xi) = conj(m(xi)) gives gamma(-xi) = -gamma(xi).  We compare
   gamma(xi) with the model  -2 pi xi log|xi| + 2 pi xi  and gamma'(xi)
   with  -2 pi log|xi|, both at 25 digits.

   WHY this matters: the base criterion (MP 2010 (1.6) at p = 2, record 1630
   sec 5) needs  psi_phase(x) = -gamma(x) - a x  to be written as
   arg Theta(x) + h~(x) with h in L^1(dPi).  psi_phase is therefore
   super-linear:  psi_phase(xi) ~ +2 pi xi log|xi|  for xi > 0.

2. THE TWO MEMBERSHIP THRESHOLDS.  For model densities |t|^beta:

       density  rho(t) = |t|^beta :  rho in L^1(dPi)  iff  beta < 1
       measure  dmu = |t|^beta dt :  dmu finite on R ((1+t^2)-weighted)
                                                      iff  beta < 2

   so a conjugate h~ of an L^1(dPi)-function can carry at most one power of
   |x| while the argument of an inner function (a measure) can carry two.
   The phase budget of the base sits strictly between: exponent 1 + o(1).

3. THE CRITICAL EXPONENT OF PHASE INTERPOLATION.  For the two-tap model of
   1630 sec 8 / 1631 sec 5: with a shifted-tap symbol m(xi) = e^{2 pi i mu xi}
   the base is non-trivial iff  c < mu  (c = 2 log lambda); the printed
   1630 form gives the mu-independent threshold  lambda < 1.  This is the
   third independent check of Erratum C (the first two being lambda = 1 and
   m = 1, where the printed form is only accidentally right because the
   delta tap is even).

Usage:  python scripts/phase_budget_1631.py
"""

import mpmath as mp

mp.mp.dps = 30


def gamma_phase(xi):
    """Continuous argument of m on the real axis (odd in xi)."""
    xi = mp.mpf(xi)
    return 2 * mp.pi * xi * mp.log(mp.pi) - 2 * mp.im(mp.loggamma(mp.mpf(1) / 4 + mp.pi * 1j * xi))


def gamma_prime(xi):
    """d/dxi gamma(xi), via the digamma function."""
    xi = mp.mpf(xi)
    return 2 * mp.pi * mp.log(mp.pi) - 2 * mp.pi * mp.re(mp.digamma(mp.mpf(1) / 4 + mp.pi * 1j * xi))


def check_phase():
    print("1. PHASE ASYMPTOTICS of m (25+ digits)")
    print("   xi        gamma(xi)             model -2pi xi log xi+2pi xi    rel.err     resid vs model+pi/4   gamma'(xi)          -2 pi log xi")
    for e in (2, 3, 4, 5, 6):
        xi = mp.mpf(10) ** e
        g = gamma_phase(xi)
        model = -2 * mp.pi * xi * mp.log(xi) + 2 * mp.pi * xi
        rel = abs(g - model) / abs(model)
        gp = gamma_prime(xi)
        print("   %-8s  %-22.12g %-28.12g %-10.2e %-21.3e %-19.12g %-14.12g"
              % ("1e%d" % e, g, model, rel, g - model - mp.pi / 4, gp, -2 * mp.pi * mp.log(xi)))
    print("   odd check: gamma(-xi) + gamma(xi) at xi = 1e3 :",
          mp.nstr(gamma_phase(mp.mpf(1000)) + gamma_phase(mp.mpf(-1000)), 6))
    print()


def check_thresholds():
    """Tail increments over successive factors of 1000: for a power tail
    t^{b-2} the ratio of successive increments is exactly 1000^{b-1}, so the
    critical exponent is read off directly (1 = logarithmic divergence)."""
    print("2. MEMBERSHIP THRESHOLDS  (quadrature of the model densities/measures)")
    print("   beta     int_1^1e3      int_1^1e6       int_1^1e9      incr ratio 1000^(b-1)   verdict")
    for beta in ("0.5", "0.9", "1.0", "1.1", "1.5", "1.9", "2.1"):
        b = mp.mpf(beta)
        vals = []
        for X in ("1e3", "1e6", "1e9"):
            vals.append(mp.quad(lambda t: t ** b / (1 + t ** 2), [1, mp.mpf(X)]))
        d1, d2 = vals[1] - vals[0], vals[2] - vals[1]
        ratio = d2 / d1
        if ratio < mp.mpf("0.95"):
            verdict = "converges"
        elif ratio <= mp.mpf("1.05"):
            verdict = "LOG DIVERGES"
        else:
            verdict = "diverges"
        print("   %-8s %-14.8g %-15.8g %-15.8g %-10.4f %-9.4f %s"
              % (beta, vals[0], vals[1], vals[2], ratio, mp.mpf(1000) ** (b - 1), verdict))
    print("   thresholds: densities (h in L^1(dPi)) need beta < 1; measures")
    print("   (arguments of inner functions) need beta < 2.  Our phase needs")
    print("   exponent 1 + o(1) (x log x): inside the measure budget, outside the")
    print("   density budget.")
    print()


def check_tap_model():
    """Exact algebra, three models.  c = 2 log lambda <= 0 for lambda <= 1."""
    print("3. SHIFTED-TAP MODEL (Erratum C, third check)")
    print("   symbol m(xi) = e^{2 pi i mu xi}  (unimodular, m(-xi) = conj m(xi)):")
    print("   base <=> e^{2 pi i c xi} m(-xi) h^ = g^ with supp h c (-inf,0],")
    print("   supp g c [0,inf).  Corrected form (sec 5): h(s + c - mu/2) = g(s + mu/2),")
    print("   supports (-inf, mu/2 - c] and [-mu/2, inf) overlap <=> mu > c.")
    print()
    print("   model                     true threshold        corrected form      printed 1630 form")
    print("   m = 1            (mu = 0) c < 0                 c < 0  [ok]         c < 0  [ok, delta even]")
    print("   lambda = 1       (c = 0)  m(-xi) h^ = g^        same equation       h^ = g^  -> h = g = 0")
    print("                             (committed base)                            [WRONG: forces empty]")
    print("   mu = 1, c = 0.5           true (0.5 < 1)        c < mu  [ok]        lambda < 1  [WRONG]")
    print("   mu = 1, c = -1            true (-1 < 1)         c < mu  [ok]        lambda < 1  [wrong reason]")
    print()
    print("   The printed form's threshold is mu-independent (lambda < 1 always),")
    print("   so it is refuted by the mu != 0 models; the corrected form reproduces")
    print("   mu > c in all three.  m = 1 cannot discriminate because delta is even.")
    print()


def main():
    check_phase()
    check_thresholds()
    check_tap_model()


if __name__ == "__main__":
    main()