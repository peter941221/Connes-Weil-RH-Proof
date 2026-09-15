# 1446 — R3 defect-series exhaustion socket

**Date:** 2026-09-14.

**Status:** FORMAL / GREEN.

**Consumer:** the healthy-`CompactLog`, B5-shaped same-owner conclusion
`0 <= C1SameOwnerWeil.qw g`, through the R3 alternating-power endpoint.

## Result

The finite defect-budget identity now has its exact infinite-stage consumer.
For a radial input, if the defect series satisfies

```text
sum'_k defect(T_b^k v) = ||v||^2 - ||r_b v||^2,
```

then the squared norms of the alternating powers tend to `||r_b v||^2`.
Records 1444 and 1445 then give both scalar endpoint inequalities, and record
1443 converts the result to zero Fejer distance and strong convergence to the
intersection projection.

## Formal declaration

`doubledShiftAlternatingProduct_sq_norm_tendsto_projection_of_defect_tsum_eq`

## Acceptance

The focused audit build log
[`026_defect_tsum_exhaustion_try2.log`](/home/peter/rh/build-logs/026_defect_tsum_exhaustion_try2.log)
reports `Build completed successfully (3178 jobs)`, zero `error:` lines,
zero `sorryAx`, and forty-two standard `Quot.sound` entries.
