# 973 — 4-fold hI cost-corrected: not a "small-constant" leaf, needs a global sup bound

Date: 2026-08-11. Status: route/effort correction (analysis; no new proof). RH NOT claimed.
See also docs/972, /968, /965, /970, /971.

## What changed vs docs/972's "very attackable, pure analysis+build"

docs/972 predicted the 4-fold `hI` (`|<int integrand| < C*||convBump||^2`, C=log4pi+gamma)
needs only CRUDE constants. A first-principles audit of the actual integrand shows the crude
factorized bound is NOT enough: replacing `0 <= conv4F <= A4` (`conv4F = 4-fold convolution
square of the real bump`) and bounding `|e^{y/2} conv4F(y) - A4| <= e^{y/2} A4 + A4` then
dividing by `den(y)=e^y-e^{-y}` leaves the mid-band `(1,4]` itself over the target:

    int_(1,4] 2 e^{y/2} A4 / (e^y-e^{-y})  ~  4 A4 (e^{-1/2}-e^{-2})/(1-e^{-1})  ~  O(11)

already ~ the whole C*A4 budget (~14.2), before the near band is added, and using the
upper bound A4 via the actual L2 norm (<4.6) only makes it worse.  So the (1,4] "mid" MUST
use the true cancellation `e^{y/2} conv4F(y) - A4 ~ < e^{y/2} A4`.  This is NOT a constant-picking
leaf; it is a genuinely new control on the shape of the 4-fold convolution square (a decay /
global-max type estimate).

## The single control that would close it (numeric-sharp)

Numerics (docs/972): max|integrand| / g4(0) = 0.50 on (0,4] and g4(0)=||convBump||^2=4.584,
so a VALID `|Re integrand| <= (1/2) * g4(0)` on (0,4] (plus the tail ~ -2 g4(0)e^{-y}, support in
[-4,4]) suffices: |J| <= (1/2) A4 * 4 + O(tail) ~ 2 A4 < C A4 (C ~ 3.1086).  The whole 4-fold hI
collapses to ONE global estimate

    | e^{y/2} conv4F(y) - A4 |  <=  (1/4) A4 (e^y - e^{-y})      on  (0,4]

where conv4F(0)=A4.  At y->0+ both sides go as A4*y/2 (sharp, boundary=max).  Proving this is a
real inequality on the explicit 4-neighbourhood of the convolution square (behavior of
e^{y/2 / conv4F vs the growing 2sinh): it is the crux, and it is NOT a Lean-assembly/small-constant
leaf.  A rigorous closure requires the conv4F-signal-growth control (derivative / log-concavity /
`sqrt`-family decay) of `conv4F = bumpF * bumpF`.

## What is still true and verified (from prior bricks)

- Direction B (prove the 4-fold owner nonzero) is still self-consistent, no depended-API change,
  numeric arch4 = +14.64 (docs/972).  It is NOT a trivial leaf: it needs the single global sup
  bound above.
- The healthy Wall-A dead-verdict docs/965 is ALREADY recorded; closing the 4-fold nonzero
  strengthens but is NOT required for the dead verdict to be documented.

## Recommendation (for Peter)

Short: invest in the conv4F shape-bound (sight, real analysis) to close the 4-fold hI; OR
accept that direction B's hI is a real-open tail and leave the Wall-A healthy arch-bridge
"dead-verdict" on the documented, still-open flow. The 2-fold close (Wall14PlateauBumpHI) is
UNCHANGED and complete.

RH NOT claimed.
