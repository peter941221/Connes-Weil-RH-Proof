# 018 — R3 unit-scale detector-root square-sum partial closure

**Date:** 2026-09-14.

**Status:** formal partial analytic brick; supporting route record, not an RH
claim.

**Consumer:** the healthy-`CompactLog`, B5-shaped statement
`0 <= C1SameOwnerWeil.qw g` for the same tower-selected detector.

## 1. Exact result

The raw selected convolution root is not used as an HS factor.  The source
module explicitly treats it as a whole-line Fourier multiplier; the legal
source-owned factor is the completed range leg
`sourceRootCompletedRangeLeftLeg`.  At the fixed unit scale, the existing
prolate theorem supplies the missing input, and the new Dev bridge proves

```text
sum'_i ||sourceRootCompletedRangeLeftLeg owner unitSoninScale (e_i)||^2 < infinity.
```

The same bridge proves the corresponding energy majorant and, using the actual
no-gap strong limit from [017](017_r3_no_gap_alternating_power_limit.md), proves
that the alternating-power defect energy on these columns tends to zero.  The
new declarations are in
`ConnesWeilRH/Dev/C1G8R3DetectorRootSquareSum.lean`:

- `sourceRootCompletedRangeLeftLeg_unit_summable`;
- `sourceRootCompletedRangeLeftLeg_unit_basisEnergy_le`;
- `doubledShiftAlternatingProduct_weighted_hs_energy_tendsto_zero_of_strong_limit`;
- `sourceRootCompletedRangeLeftLeg_unit_weighted_hs_energy_tendsto_zero`.

This is a formal result, not a numerical observation.  Batch acceptance is
`build-logs/1451_detector_root_try2.log`: `Build completed successfully
(3280 jobs)`, zero `error:` lines, zero `sorryAx`, and four audited standard
axiom sets.

## 2. The hard boundary that remains

This closes only the prolate-range leg.  The source normal form identifies the
independent leakage leg as

```text
rootConvolution owner * (sourceBandProjection lambda - sourceProlateRemainder lambda).
```

The existing prolate square-sum does not control that full band-minus-prolate
input.  The common-right finite-Euler crossing is a second independent leg.
Thus the full detector-root square-sum and the same-basis signed trace witness
are still open; the new result must not be promoted to a complete R3 trace
estimate.

Record 1452 now supplies the exact structural reduction for the leakage leg:
on the same carrier it is the selected root conjugated against the doubled-
shift defect `p_b - T_b`, with `T_b = p_b * q_1 * p_b`; see
[019](019_r3_leakage_doubled_shift_normal_form.md).  The next proof target is
an estimate for that concrete defect, with the finite-Euler/common-right leg
kept in the same coupled owner.  Record 1453 now proves the defect is a
positive contraction and gives its exact complementary-leakage energy, but
does not supply HS smoothing for the selected root times the defect.  A proof
that simply declares the raw convolution root Hilbert--Schmidt is rejected by
this record.
