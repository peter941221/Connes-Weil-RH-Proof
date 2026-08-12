# 992 — 4-fold hI crux: (1/4) bound TRUE, tight ONLY at y=0; exact second-order handicap

Date: 2026-08-11. Status: independent numeric audit + crux exact localization (no new Lean proof). RH NOT claimed.
See also docs/972 (index finding), /973 (cost vocality), /968, /965.

## Headline (confirms and sharpens docs/973)

An independent mpmath/numpy re-probe of `conv4F(y) = (bumpF * bumpF)(y)` (bump support [-1,1],
F= 2-fold, 4-fold support [-4,4]) over (0,4] confirms:

- A4 = g4(0) = 4.58762 ; bumpF(0) = 1.8375
- max |integrand| / A4 = 0.4997 (matches docs/973's 0.50)
- The global bound  |e^{y/2} conv4F(y) - A4| <= (1/4) A4 (e^y - e^{-y})   holds on (0,4]
  with numeric worst ratio = 0.99433, at y -> 0+ (tight there).

## The exact handicap: first-order equality, second-order governs

At y=0 both sides are EQUAL and have EQUAL slope:

- LHS ~ A4 * (y/2)  (from e^{y/2}*A4 - A4, conv4F(0)=A4, conv4F'(0+)? even => conv4F'(0)=0)
   so  e^{y/2}conv4F(y) - A4 ~ A4 y/2
- RHS = (1/4) A4 (e^y - e^{-y}) ~ (1/4)A4(2y) = A4 y/2

=> slope equality A4/2 == A4/2.  The inequality therefore holds iff the SECOND order
difference is nonnegative:

    H(y) := A4 + (A4/4)(e^y - e^{-y}) - e^{y/2} conv4F(y) >= 0 on (0,4],  H(0)=0, H''(0) > 0.

Numeric: (conv4F)''(0) / A4 = -0.8120, R''(0) = (1/4) + q''(0) = -0.5602,
(bound)''(0) = (1/4)(e^0 + e^0) = 1/2, so H''(0) = 0.5 - (-0.560) = +1.062 > 0.  Confirmed.

So NO constant-relaxation trick helps at the origin (every scalar c in c*(e^y-e^{-y})/4 keeps the same
first-order slope A4/2).  Removing the crux REQUIRES a genuine decay/concavity (second-derivative)
control on the 4-fold convolution `conv4F` — exactly the "new shape analysis" docs/973 flagged.

## Huge slack downstream (so the pointwise bound is overkill if we get ANY decay)

The pointwise (1/4) bound -> |I4| <= (1/2)A4 * 4 = 2 A4, while C*A4 ~ 3.1086 A4: 1.5x margin.
The tight (1/4) point is NOT needed.  A decay bound on conv4F with ANY positive rate suffices.

## What is already in Lean (fast path, no new math)

Wall14Conv4Base.lean already provides: conv4F_eq_integral_small, A4_nonneg, conv4F_nonneg,
conv4F_even, conv4F_eq_zero_of_four_le_abs, conv4F_mul_exp_half.
Missing and provable (no curvature): conv4F <= A4 (CS / 2ab<=a^2+b^2 over the compact support).

## The single crux lemma (hand-off target)

(meth4LeBound : forall y, 0 < y -> y <= 4 ->
   Real.exp (y/2) * conv4F y <= A4 + (1/4)*A4*(Real.exp y - Real.exp (- y)))
plus the mirror lower-bound to cover |*|.  Closing H''(0)>0 + a compactness/decay step on conv4F
is the remaining genuinely-new analysis.  This IS the docs/973 crux, now pinned to a single
second-order statement.
