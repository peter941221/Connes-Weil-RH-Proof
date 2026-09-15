# 1491 — The source-prolate pullback in the G8 boundary estimate is zero

Date: 2026-09-16.

**Consumer:** the same-owner G8 visible-boundary detector-root energy
condition needed for the healthy-`CompactLog`, B5-shaped semi-local
positivity branch.

**Evidence:** formal Lean declarations
[`sourceProlateHilbertSchmidtFactor_comp_sourceInclusion_eq_zero`](../../ConnesWeilRH/Dev/C1G8P1SourceProlatePullbackZero.lean)
and
[`g8MetricVisibleBoundaryCoframe_comp_sourceProlatePullback_eq_zero`](../../ConnesWeilRH/Dev/C1G8P1SourceProlatePullbackZero.lean),
with paired audit
[`C1G8P1SourceProlatePullbackZeroAudit.lean`](../../ConnesWeilRH/Dev/C1G8P1SourceProlatePullbackZeroAudit.lean).
Acceptance log: `0916_g8_prolate_pullback_zero_try2.log`; build completed
successfully (4049 jobs), zero `error:` lines, zero `sorryAx`, and two
standard-axiom audit terminators.

The explicit prolate factor is the Fourier-support projection composed with
the source-band projection. The source inclusion lands in the source-Sonin
projection, which the source-band projection annihilates. Consequently the
prolate factor composed with the source inclusion is zero, and so is the
visible-boundary coframe composed with the pullback
`sourceInclusion† * sourceProlateFactor * sourceInclusion`.

This classifies the existing estimate
`g8MetricVisibleBoundaryCoframe_comp_sourceProlateFactor_summable_normSq`:
its supplied input is zero, so its summability conclusion is true but does not
estimate the actual root/coframe columns in `hBoundary`. It does not refute
`hBoundary`; it removes this prolate-pullback estimate as evidence for it. A
valid boundary energy proof needs a nonzero input that matches the actual
same-basis root/coframe columns. G8 readback, the semi-local sign, C3, and RH
remain open.
