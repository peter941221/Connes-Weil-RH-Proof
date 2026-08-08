# 888 - Arch phase gate: elementary closed sandwich for arg Gamma(1+i/2)

Date: 2026-08-08 (rev 2). Status: analytic bottom fully reduced to an elementary series
sandwich; Lean-internal closure is an IN-REPO real-analysis Stirling/integral remainder
proof (NOT an external dependency).

## 0. Bottom line

The route-1 arch sign at a=1 reduces (axiom-clean Lean) to

    Re( Gamma(1 + I/2)^4 ) >= 0   <==>   (Re[Gamma(1+I/2)/conj Gamma(1+I/2)])^2 >= 1/2

i.e. |arg Gamma(1+I/2)| <= pi/8  (ArchPhaseWindow.gammaPhase_window).  The modulus side is
closed: |Gamma(1+I/2)|^2 = pi/(2*sinh(pi/2)) (GammaImaginaryAxisModulus).  The only open
content is the phase.  This document proves, at the analytic level with a certified
high-precision numerical sandwich, that the phase is inside [-pi/8, pi/8].  No Stirling /
arg-Gamma is needed for the MATH; the phase is an explicit elementary series plus two
constants.

What remains for LEAN closure is to formalize that phase inside the repo via a real
Stirling/Euler-Maclaurin/integral-remainder bound (Binet-style) - a genuine in-repo
analysis proof, not an external library dependency.  We must not inflate this into "needs
mathlib extension".

## 1. The elementary phase identity

For z = 1 + I/2, the Weierstrass partial-product form of Gamma gives formally

    Gamma(1+z) = exp(-gamma z)/z * Product_{n>=1} (1 + z/n)^{-1} * exp(z/n)

Taking arguments, with z = 1 + I/2 (all factors in the closed right half-plane):

    arg Gamma(1+z) = -gamma/2 - atan(1/2) + S

with

    S := Sum_{n>=1} [ 1/(2n) - atan( 1/(2(n+1)) ) ].

Numeric verification (mpmath): arg Gamma(1+I/2) = -0.2440583, formula -0.2440633 (S at 2e5).

## 2. Certified sandwich of S

With gamma/2 + atan(1/2) = 0.75225544145157254...

    arg >= -pi/8  <=>  S >= gamma/2 + atan(1/2) - pi/8 = 0.3595563597528...
    arg <=  pi/8  <=>  S <= gamma/2 + atan(1/2) + pi/8 = 1.1449545231503...

Lower bound (binding): S >= S_3 (first 3 terms; S_3 = 0.3821843315784... >= 0.35956...
  margin ~0.02263).
Upper bound (loose): atan(x) >= x - x^3/3 extracts a telescoping part;
  S <= 0.50841904... <= 1.14495...  (margin ~0.637).

So S in [0.38218, 0.50842] inside the required band, and |arg| is in (-pi/8, pi/8).

## 3. What stays to close in Lean (in-repo, honest)

To certify the lower/upper bound of |arg Gamma(1+I/2)| axiom-clean in this repo one needs
a real, in-repo analysis proof, e.g.:
  (a) a Stirling/Euler-Maclaurin (or Binet) bound on log|Gamma(s)| for Re s > 0 with an
      explicit remainder on the compact strip { |Im| <= 1, 1/2 <= Re <= 1 }, plus
  (b) the atan log/gamma/pithe exact decimals, each provable from mathlib raw reals.
This is a completed piece of real-analysis formalization - sizable, but entirely self-
contained; it does not require anyone else to add a library.

## 5. Status

- ANALYTIC: closed at the elementary level; phase of Gamma(1+I/2) is rigorously inside
  (-pi/8, pi/8).
- LEAN: becoming an in-repo Stirling/integral-remainder proof task (no external ask).
- RH: not claimed.
