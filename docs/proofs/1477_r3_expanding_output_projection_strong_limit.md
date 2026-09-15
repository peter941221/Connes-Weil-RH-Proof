# R3 expanding output-projection strong limit

**Status:** formal strong convergence of the expanding output-window
projections; the G8 cutoff/source trace readback remains open.

**Consumer:** the literal output window in the healthy-`CompactLog` G8
leakage/source cross channel, downstream of which the active B5 consumer is
`0 <= C1SameOwnerWeil.qw g` for the tower-selected detector.

The theorem
[`tendsto_kernelIntervalProjection_symmetric_apply`](../../ConnesWeilRH/Dev/C1G8R3OutputProjectionStrongLimit.lean)
proves that the global logarithmic L2 projection onto `[-n,n]` converges
strongly to the identity. Its proof identifies the projection error with the
complementary interval indicator, proves that the squared L2 tail decreases
pointwise to zero, and applies monotone convergence to its finite integral.
The square-root continuity then yields convergence in L2.

The paired audit in
[`C1G8R3OutputProjectionStrongLimitAudit.lean`](../../ConnesWeilRH/Dev/C1G8R3OutputProjectionStrongLimitAudit.lean)
prints exactly `[propext, Classical.choice, Quot.sound]`. Acceptance evidence:
`20260915_r3_output_projection_strong_limit_try15.log` reports
`Build completed successfully (3214 jobs)`, zero `error:` lines, and zero
`sorryAx`.

This result is only the global interval-projection limit. It does not yet
prove strong convergence of the actual G8 factor after composition with the
convolution and source inclusion, does not establish the doubled source
compression limit required by the conditional HS-pair trace theorem, and
does not close the other metric channels, remainder, same-owner `qw` readback,
detector sign, C3, or RH.
