# Record 2498 — formal split envelope for negative exponentials

The owner-cell premise contains factors of the form
`Real.exp (-30 / (1 - a^2))`.  A global `exp (-30)` bound was ruled out by
record 2497.  This record adds the reusable analytic split
`z = n + r`, with `n : ℕ` and `0 ≤ r ≤ 1`:

`exp (-z) <= E^n * (Taylor20(r) + Taylor20Error)`.

Here `E = 3678794411714424 / 10^16` is a formally proved upper bound for
`exp(-1)`, and the unit-interval Taylor enclosure is the existing
`C1ScaledExpRationalEnvelope.expTaylor20_error` theorem.  The declarations
are in `C1RouteAExpSplit2498.lean`; its audit builds successfully (3667/3667)
and reports only `[propext, Classical.choice, Quot.sound]`.

This is an analytic building block, not yet the 640-cell hcell proof.  The
remaining work is to generate exact rational `n,r` decompositions for each
owner/family/cell, propagate the split bound through `weightedCurvature2348`,
and reprice the resulting Taylor slack before replacing the 2496 payload.
No producer GO or RH claim is made.
