# 1451 — R3 unit-scale detector-root square-sum partial closure

**Date:** 2026-09-14.

**Evidence class:** FORMAL ANALYTIC BRICK.

**Consumer:** the healthy-`CompactLog`, B5-shaped same-owner conclusion
`0 <= C1SameOwnerWeil.qw g`.

## Result

The raw selected convolution root is not promoted to a Hilbert--Schmidt
factor.  The exact source-owned factor used here is the completed range leg
`sourceRootCompletedRangeLeftLeg`. At `unitSoninScale`, its column square-sum
follows from the already formal fixed-source prolate square-sum theorem. The
new bridge also proves the corresponding energy majorant and feeds the actual
no-gap strong power limit directly into the dominated-convergence transfer,
without a separate defect-series premise.

Owning module:
`ConnesWeilRH/Dev/C1G8R3DetectorRootSquareSum.lean`.
Paired audit:
`ConnesWeilRH/Dev/C1G8R3DetectorRootSquareSumAudit.lean`.

## Boundary

This closes only the prolate-range leg. The independent source normal form for
the leakage leg is the selected root applied to
`sourceBandProjection - sourceProlateRemainder`; the existing prolate HS
certificate does not control that input. The common-right finite-Euler
crossing is another independent leg. Therefore the full detector-root
square-sum, same-basis signed trace witness, G8 readback, R3, and RH remain
open.

## Acceptance

`build-logs/1451_detector_root_try2.log` reports:

```text
Build completed successfully (3280 jobs)
error: 0
sorryAx: 0
```

The paired audit prints four declarations, all with
`[propext, Classical.choice, Quot.sound]`.
