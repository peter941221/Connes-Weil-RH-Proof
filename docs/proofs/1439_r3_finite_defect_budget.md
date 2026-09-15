# 1439 — R3 finite defect budget

**Date:** 2026-09-14.

**Status:** FORMAL / GREEN.

**Consumer:** the healthy-`CompactLog`, B5-shaped same-owner conclusion
`0 <= C1SameOwnerWeil.qw g`, through the R3 endpoint bridge.

## Result

The power-bridge leaf defines the scalar defect energy of the actual
two-projection step and proves, for every radial input `v` and `n : Nat`,

```text
sum_{k < n} defect(T_b^k v)
  = ||v||^2 - ||T_b^n v||^2.
```

The proof uses the exact one-step Pythagorean identity from record 1438,
the fact that every alternating power remains in the radial subspace, and
finite induction. No estimate, spectral gap, trace-class premise, detector
sign, `SourceRH`, or RH conclusion is used.

## Boundary

The identity is finite-stage only. Passing to `n -> infinity` still requires
an analytic theorem that identifies the limiting defect budget with the
non-intersection component and yields `T_b^n v -> r_b v`. The finite budget
does not supply that theorem by itself.

## Acceptance

The paired audit build log
[`019_defect_zero_try7.log`](/home/peter/rh/build-logs/019_defect_zero_try7.log)
reports `Build completed successfully (3178 jobs)`, zero `error:` lines,
zero `sorryAx`, and twenty-five standard `Quot.sound` entries.
It also proves that each individual defect energy tends to zero, via the
summability of the nonnegative defect series, and that the two nonnegative
orthogonal defect components tend to zero separately by squeezing.
