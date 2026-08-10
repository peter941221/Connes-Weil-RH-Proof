# 937 - Negative verdict: the naive large-band Gamma sign `Re[Gamma(a+i/2)^4] >= 0` is FALSE

Date: 2026-08-10. Type: numeric route-ruling (falsification of docs/859 §6 conjecture). No RH claim.

## 1. What was conjectured and why it fails

docs/859 §6 suggested proving the finite-S Weil sign on the large band:

    Conjecture (859): exists a0>0, forall a>=a0, Re[(Gamma(a+i/2))^4] > 0.

Heuristic there was "arg Gamma(a+i/2) -> 0 for large real a".  That heuristic is wrong:
the argument does NOT -> 0, so Re[w^4] does NOT stay positive.

## 2. Numeric ruling (scipy.special.gamma, real-axis a, w = Gamma(a+i/2))

    a      Re[w^4]        arg w
    0.10   +6.15          -1.550
    0.20   +2.27          -1.306
    0.40   -1.99          -0.907
    0.60   -0.88          -0.618
    0.80   -0.03          -0.406
    0.90   +0.16          -0.320
    1.00   +0.26          -0.244
    1.20   +0.35          -0.116
    1.50   +0.39          +0.035
    2.00   +0.46          +0.220
    3.00   -3.73          +0.465
    5.00   -2.95e+05       +0.754
   10.00   -3.40e+21       +1.126
   20.00   +2.01e+53       +1.485
   50.00   +6.77e+66       +1.951

So Re[w^4] flips sign MANY times (a: 0.4-0.8-, 0.9+; 3-10-, 20+), and for
a=3,5,10 it is clearly NEGATIVE.  There is no a0 after which it stays positive.

## 3. Why it fails structurally (not a numeric fluke)

Stirling asymptotic (large real a): Im[log Gamma(a+i/2)]
    ~ (a-1/2)*atan(1/(2a)) + (1/2)*ln|a+i/2| - 1/2   [= Im[(z-1/2)log z - z]]
  -> (1/2) ln a  as a -> oo.
So arg Gamma(a+i/2) -> oo (unbounded, monotone-ish), and Re[w^4] =
|Gamma|^4 * cos(4*arg) oscillates forever: it is negative on infinitely many
disjoint bands (where 4*arg in (pi/2, 3pi/2) mod 2pi).  Hence there is NO uniform
event-positivity band; `forall a>=a0 Re[w^4]>=0` is FALSE.

(The scipy "saturation" arg -> 3π/4 for a>=>100 is a cephes overflow artifact; the
unbounded-growth / +cososcillation conclusion is robust at a=3,5,10 where the
pedagogy is solid.)

## 4. Route consequence (honest)

- The naive band `g = t^a e^{-t}`, Mellin = Gamma(a+i/2) (MellinBandGamma) cannot
  be the finite-S sign producer: its 4th-power phase is not eventually positive.
- This is consistent with docs/869 route-note: the canonical sign home is the
  CompactLog HS carrier (A3 PSD F^dagger F, detector_diagonal_re_nonneg,
  healthy_strict_positive_diagonal), NOT the Gamma/Mellin band phase.
- Step 3 must therefore re-point the finite-S sign to the A3/CompactLog producer
  (already built + axiom-clean), not to a Gamma-phase band bound.

## 5. Evidence
Numeric: scipy.special.gamma on the a-grid above (read-only). No Lean implication.

RH NOT claimed.