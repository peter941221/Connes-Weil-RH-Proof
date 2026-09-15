# 1440 — R3 defect-norm decay and asymptotic regularity

**Date:** 2026-09-14.

**Status:** FORMAL / GREEN.

**Consumer:** the healthy-`CompactLog`, B5-shaped same-owner conclusion
`0 <= C1SameOwnerWeil.qw g`, through the R3 endpoint bridge.

## Result

The power-bridge leaf now proves three layers beyond the scalar defect budget:

1. a nonnegative squared norm tending to zero implies the corresponding norm
   tends to zero;
2. the Fourier and radial projection defects of every alternating iterate
   tend to zero in norm separately;
3. the one-step residual is bounded by the sum of those two defect norms, so
   for every radial input `v`,

```text
||T_b^(n+1) v - T_b^n v|| -> 0.
```

The residual estimate is obtained from the orthogonal-complement projection
identity and the triangle inequality. No angle gap, trace-class estimate,
detector sign, `SourceRH`, or RH conclusion is used.

## Boundary

Asymptotic regularity is strictly weaker than the required vector convergence:
the result does not show that the orbit is Cauchy, nor that its limit is the
doubled-shift Sonin intersection projection `r_b v`. The next analytic target
is an infinite-stage exhaustion/finite-dimensional spectral argument that
identifies the orbit limit without assuming a uniform Friedrichs-angle gap.

## Acceptance

The paired audit build log
[`020_defect_norm_try8.log`](/home/peter/rh/build-logs/020_defect_norm_try8.log)
reports `Build completed successfully (3178 jobs)`, zero `error:` lines,
zero `sorryAx`, and thirty-two standard `Quot.sound` entries.
