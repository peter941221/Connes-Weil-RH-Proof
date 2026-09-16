# 018 — R3 detector-root range square-sum partial closure

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
unit-scale result is now extended to every selected scale: the source prolate
square-sum transfers from the relative factor through the exact translation
conjugacy, and the actual completed range leg gets the same-basis square-sum,
weighted energy limit, and positive-composition trace-class conclusion.  See
[028](028_r3_moving_scale_detector_root_range_energy.md) and
[1465](../proofs/1465_r3_moving_scale_detector_root_range_energy.md).  The
unit-scale declarations are in
`ConnesWeilRH/Dev/C1G8R3DetectorRootSquareSum.lean`:

- `sourceRootCompletedRangeLeftLeg_unit_summable`;
- `sourceRootCompletedRangeLeftLeg_unit_basisEnergy_le`;
- `doubledShiftAlternatingProduct_weighted_hs_energy_tendsto_zero_of_strong_limit`;
- `sourceRootCompletedRangeLeftLeg_unit_weighted_hs_energy_tendsto_zero`.

The all-scale declarations are in
`ConnesWeilRH/Dev/C1G8R3ScaleDetectorRootSquareSum.lean`:

- `sourceProlateHilbertSchmidtFactor_summable_all_scales`;
- `sourceRootCompletedRangeLeftLeg_summable_all_scales`;
- `sourceRootCompletedRangeLeftLeg_basisEnergy_le_all_scales`;
- `sourceRootCompletedRangeLeftLeg_weighted_hs_energy_tendsto_zero_all_scales`;
- `sourceRootCompletedRangeLeftLeg_positiveComposition_isTraceClassAlong_all_scales`.

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

Record 1484 formally factors each actual-cutoff G8 diagonal channel as the
positive square of its selected detector-root/coframe/cutoff leg and reads its
ordinary trace as the same-basis column-energy sum. This identifies the
uniform square-sum/convergence required by the two diagonal limits; it does
not supply that estimate. The survivor/boundary mixed trace limit is formal
in record 1483, but does not imply either diagonal bound.

Record 1487 adds a formal lower bound on the separate unit-scale leakage leg
along right translates of its own compact source test: when the test detects
a Laplace value, the leakage output norm is eventually at least half the
nonzero selected-root output norm. This is ambient `finiteSCarrier` evidence
for a lower-energy orbit. Record 1488 now formalizes a normalized orthonormal
subsequence of separated translates. Record 1489 combines that sequence with
the lower bound and proves that the actual ambient leakage outputs have a
non-summable squared-norm sequence. This rules out using an ambient
Hilbert--Schmidt estimate for this raw leg as the missing argument. The orbit
is still not identified with the named source basis or the source-compressed
G8 diagonal leg, so both diagonal estimates, the cutoff-to-trace readback, and
the full same-owner trace estimate remain open.

Record 1490 sharpens this interface boundary. The source-Sonin projection of
the separated ambient orbit itself tends to zero in norm, because the unit
Fourier-support projection decays along right translations and the complete
source projection is absorbed by it. Therefore projecting these ambient
vectors and renormalizing cannot transfer their leakage lower bound to the
G8 source-carrier columns. This closes that direct transfer attempt only; it
does not bound or refute either actual G8 diagonal energy sum. The next
producer must use the source-carrier columns after the actual compressed
convolution/coframe, rather than an ambient orbit projection. See
[proof record 1490](../proofs/1490_g8_source_projection_translated_orbit_decay.md).

Record 1491 audits one proposed source-carrier estimate. The existing G8
visible-boundary summability lemma precomposes the coframe with the pullback
`sourceInclusion† * sourceProlateFactor * sourceInclusion`; that operator is
formally zero because the prolate factor is supported on the quotient band
annihilated by the source-Sonin inclusion. The lemma therefore supplies no
bound for the actual `hBoundary` columns. This does not refute `hBoundary`;
that genuine same-basis root/coframe estimate remains open. See
[proof record 1491](../proofs/1491_g8_source_prolate_pullback_zero.md).

Record 1492 formally splits the aggregate G8 boundary root energy through the
finite visible-prime Schur--polar outputs: square-summability of each rooted
output on the same source basis implies `hBoundary`. Record 1493 wires this
condition into the actual four-channel physical metric trace-limit consumer.
Neither record estimates the individual rooted outputs, so the actual
boundary energy and unconditional trace limit remain open. See [proof record
1492](../proofs/1492_g8_boundary_energy_finite_output_reduction.md) and
[proof record 1493](../proofs/1493_g8_boundary_output_trace_consumer.md).

Record 1494 formally decomposes the selected-root source-Sonin leakage into
the radial-support complement and the internal radial-but-non-Sonin gap, on
the same `finiteSCarrier` owner. Record 1495 then proves the exact support
identity for the zero-boundary crossing and its translation to the actual
radial cutoff after composing with the actual source inclusion. Record 1496
proves square-summability of the actual radial-boundary outputs on any named
source basis. The internal-gap estimate, the separate finite visible-prime
G8 boundary-output energies, actual G8 diagonal energies, and trace/readback
remain open. See [proof records
1494](../proofs/1494_r3_radial_boundary_internal_gap_split.md),
[1495](../proofs/1495_r3_radial_boundary_finite_window_identity.md), and
[1496](../proofs/1496_r3_radial_boundary_source_energy.md).
