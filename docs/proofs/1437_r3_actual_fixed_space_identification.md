# 1437 — R3 actual alternating-product fixed space

**Date:** 2026-09-14.

**Status:** FORMAL / GREEN.

**Consumer:** the healthy-`CompactLog`, B5-shaped same-owner conclusion
`0 <= C1SameOwnerWeil.qw g` for the tower-selected detector, through the R3
weighted endpoint trace bridge and its existing G8 readback consumer.

## Result

In `C1G8R3PowerProjectionBridge.lean`, for the actual finite-S carrier and
every real `b`, the formal theorem
`doubledShiftAlternatingProduct_fixed_iff_mem_intersection` proves:

```text
(p_b q p_b) v = v  if and only if
v belongs to Ran(p_b) intersect Ran(q).
```

The right-to-left implication was the existing intersection fixing result.
For the new left-to-right implication, the proof first applies `p_b` to the
fixed-vector equation and uses idempotence to obtain `p_b v = v`.  The two
projection contractions then give equality of the norms of `q v` and `v`.
Mathlib's orthogonal-projection norm characterization places `v` in
`Ran(q)`.  Thus both memberships are obtained without a spectral gap or a
convergence premise.

The companion theorem
`doubledShiftRadialProjection_comp_doubledShiftAlternatingProduct` supplies
the absorption identity used in that proof.

## Boundary

This identifies the spectral fixed space at value one.  It does **not** prove
the strong limit of the powers, operator-norm convergence, a Friedrichs-angle
gap, a Hilbert--Schmidt detector-root sum, trace classness, a G8 readback, or
an RH conclusion.  The next analytic target remains the classical
angle-free alternating-projection strong-limit theorem on this exact carrier.

## Acceptance

The paired audit prints axioms for both declarations.  The unified R3 batch
log [`016_r3_unified_batch.log`](/home/peter/rh/build-logs/016_r3_unified_batch.log)
reports `Build completed successfully (3182 jobs)`, zero `error:` lines,
zero `sorryAx`, and twenty-eight standard `Quot.sound` audit entries across
the finite-stage, strong-to-HS, and power-bridge audit leaves.
