# 1465 — R3 moving-scale completed detector-root range energy

**Date:** 2026-09-15.

**Consumer:** the same healthy `CompactLog` B5 detector selected against a
hypothetical off-line zero, with its same finite visible-prime family.  The
target remains detector-specific semi-local `0 <= C1SameOwnerWeil.qw g` and
the canonical `G8SameOwnerReadbackData` owner; no universal B1 statement is
used.

## Formal result

The all-scale relative-prolate factor square-sum from [1463](1463_r3_moving_scale_prolate_strict_angle.md)
now transports back to the actual source prolate factor by the exact
translation conjugacy.  On the actual source carrier and for every selected
Sonin scale, the completed range leg
`sourceRootCompletedRangeLeftLeg` has a square-summable column family on any
named Hilbert basis.  Its basis energy is bounded by the selected root norm
squared times the source-prolate column energy.

Combining this all-scale square-sum with the formal no-gap strong limit from
[1450](1450_r3_no_gap_alternating_power_limit.md) proves that the
alternating-power defect energy of the completed range-leg columns tends to
zero at every selected scale.  The positive composition of this actual
completed range leg is also `IsTraceClassAlong` the same basis.

The paired audit checks these declarations:

- `sourceProlateHilbertSchmidtFactor_summable_all_scales`
- `sourceRootCompletedRangeLeftLeg_summable_all_scales`
- `sourceRootCompletedRangeLeftLeg_basisEnergy_le_all_scales`
- `sourceRootCompletedRangeLeftLeg_weighted_hs_energy_tendsto_zero_all_scales`
- `sourceRootCompletedRangeLeftLeg_positiveComposition_isTraceClassAlong_all_scales`

## Remaining boundary

This closes only the actual completed prolate-range leg.  The doubled-shift
leakage leg and common-right finite-Euler leg remain independent; this result
does not give the full signed detector-root trace, the vanishing G8 cutoff
remainder, or the same-owner trace-to-`qw` readback.  Detector-specific
semi-local positivity, C3, and RH therefore remain open.

## Acceptance

`C1G8R3ScaleDetectorRootSquareSum.lean` and its paired audit completed in
`20260915_r3_scaled_detector_root_try2.log`: 3287 jobs, zero `error:` lines,
zero `sorryAx`, and five `Quot.sound]` audit terminators.  Each declaration
has exactly `[propext, Classical.choice, Quot.sound]`.
