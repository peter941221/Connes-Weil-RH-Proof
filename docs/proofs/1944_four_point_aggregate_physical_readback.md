# 1944 — Four-point aggregate physical readback

Date: 2026-09-24

## Result

`C1FourPointAggregatePhysicalReadback` formally attaches the four-channel
expansion to the actual two-span owner
`(spanObj ![A, B] ![(1 : ℝ), -lam]).convolutionSquare` and its own
`globalPrimeIndexSet`. The finite prime sum is therefore read back as the
sum of the A-A, A-B, B-A, and B-B physical channels with coefficients
`1`, `-lam`, `-lam`, and `lam^2`.

The module provides both the bilateral-profile form and the direct physical-
integral form. No original-orbit owner, ambient cutoff, or replacement prime
set is introduced.

## Route impact

This strictly reduces the live four-point C3' obligation: the opaque
`finitePrimeSum` term is gone from the selected span owner, leaving only a
finite signed four-channel budget. The strict sign or uniform margin is still
open; this record is a formal owner-specific reduction, not a positivity
theorem and not an RH claim.

## Verification

```text
20260924_fourpoint_aggregate_readback20.log: Build completed successfully (3790 jobs).
axioms: [propext, Classical.choice, Quot.sound]
sorryAx: none
```
