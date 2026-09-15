# 1447 — R3 defect-series / scalar-endpoint equivalence

**Date:** 2026-09-14.

**Status:** FORMAL / GREEN.

**Consumer:** the healthy-`CompactLog`, B5-shaped same-owner conclusion
`0 <= C1SameOwnerWeil.qw g`, through the R3 alternating-power endpoint.

## Result

For every radial input, the remaining no-gap condition is exactly one
equivalence, not two unrelated estimates:

```text
sum'_k defect(T_b^k v) = ||v||^2 - ||r_b v||^2
  iff
ciInf_n ||T_b^n v|| = ||r_b v||.
```

The forward direction uses the finite defect budget, squared-norm convergence,
and the two projection endpoint inequalities. The reverse direction takes the
limit of the same finite budget identity and identifies the series sum by
uniqueness of limits. Combining this with records 1443–1445 gives the strong
endpoint consumer without importing a Friedrichs-angle gap.

## Formal declaration

`doubledShiftAlternatingProduct_defect_tsum_eq_iff_scalar_endpoint`

## Acceptance

The focused audit build log
[`027_defect_tsum_iff_try1.log`](/home/peter/rh/build-logs/027_defect_tsum_iff_try1.log)
reports `Build completed successfully (3178 jobs)`, zero `error:` lines,
zero `sorryAx`, and forty-three standard `Quot.sound` entries.
