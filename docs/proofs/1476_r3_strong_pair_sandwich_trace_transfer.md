# 1476 — R3 strong-sandwich trace transfer for an HS pair

**Date:** 2026-09-15.

**Status:** formal conditional trace-transfer theorem; G8 cutoff/readback remains open.

**Consumer:** the detector-selected healthy-`CompactLog` B5 goal
`0 <= C1SameOwnerWeil.qw g`, followed by the existing `SourceRH` contradiction.

## Result

`C1G8R3StrongTracePairTransfer.lean` proves
`tendsto_ordinaryTraceAlong_pairSandwich_of_strong`. For one fixed
`BasisHilbertSchmidtPairData`, if the doubled cutoffs `C_n C_n†` have a common
operator-norm bound and converge pointwise to `C C†`, the ordinary trace of
the pair's cutoff sandwich converges to the trace of its limiting sandwich.

The proof cycles each trace to the target basis. Its diagonal terms are bounded
by the product of the two fixed adjoint Hilbert--Schmidt column norms, scaled
by the common operator bound. Cauchy--Schwarz makes this a summable majorant,
so dominated convergence applies to the trace series. No positivity or sign
assumption enters.

The theorem is instantiated as
`tendsto_ordinaryTraceAlong_sourceBandGramResponse_sandwich` using the existing
three-branch pair owner of `sourceBandGramResponse`. Thus this P1 channel has a
direct conditional trace-transfer result on its fixed source-Sonin owner.

## Boundary

The hypotheses have not been proved for the actual G8 window cutoff. In
`g8CutoffPairData`, the finite-window factor
`fullBoundaryPositiveOperator owner.sourceTest ...` varies with the window and
is placed around `g8AdjointShearGram` on the ambient carrier. This is not the
fixed P1 three-branch pair with a source-side sandwich from this theorem.
There is no cutoff/source identity, remainder limit, `qw` readback, R3 sign,
C3 result, or RH conclusion here. The route-level G8 readback remains open.

## Acceptance

Focused log: `20260915_r3_strong_trace_pair_transfer_try10.log` (WSL ext4 build log).

- `Build completed successfully (3213 jobs)`
- zero `error:` lines and zero `sorryAx`
- two audited declarations, each with only
  `[propext, Classical.choice, Quot.sound]`
