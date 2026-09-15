# 1448 — R3 defect-series / strong-endpoint equivalence

**Date:** 2026-09-14.

**Status:** FORMAL / GREEN.

**Consumer:** the healthy-`CompactLog`, B5-shaped same-owner conclusion
`0 <= C1SameOwnerWeil.qw g`, through the R3 alternating-power endpoint.

## Result

For every radial input, the exact finite defect series is equivalent to the
actual strong endpoint:

```text
sum'_k defect(T_b^k v) = ||v||^2 - ||r_b v||^2
  iff
T_b^n v -> r_b v strongly.
```

The forward direction passes through the scalar endpoint equivalence and the
exact squared-distance identity. The reverse direction takes norms of the
strong limit and applies the scalar-endpoint equivalence. Thus the alternating
projection part of R3 has one precise missing analytic statement: prove the
defect-series exhaustion equality. No Friedrichs-angle gap is introduced.

## Formal declarations

* `doubledShiftAlternatingProduct_tendsto_intersectionProjection_of_scalar_endpoint`;
* `doubledShiftAlternatingProduct_defect_tsum_eq_iff_strong_endpoint`.

## Acceptance

The focused audit build log
[`028_defect_strong_iff_try2.log`](/home/peter/rh/build-logs/028_defect_strong_iff_try2.log)
reports `Build completed successfully (3178 jobs)`, zero `error:` lines,
zero `sorryAx`, and forty-five standard `Quot.sound` entries.
