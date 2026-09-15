# 1492 — G8 boundary root energy reduces to finite prime outputs

Date: 2026-09-16.

**Consumer:** the same-owner visible-boundary square-summability condition
needed by the actual G8 physical metric trace limit on the healthy-
`CompactLog`, B5-shaped route.

**Evidence:** formal Lean declarations
[`summable_normSq_list_sum_of_each`](../../ConnesWeilRH/Dev/C1G8P1BoundaryRootEnergyReduction.lean),
[`rootConvolution_comp_list_sum_eq_list_sum_comp`](../../ConnesWeilRH/Dev/C1G8P1BoundaryRootEnergyReduction.lean),
and
[`g8MetricVisibleBoundary_root_energy_summable_of_each_output`](../../ConnesWeilRH/Dev/C1G8P1BoundaryRootEnergyReduction.lean),
with paired audit
[`C1G8P1BoundaryRootEnergyReductionAudit.lean`](../../ConnesWeilRH/Dev/C1G8P1BoundaryRootEnergyReductionAudit.lean).
Acceptance log: `0916_g8_boundary_energy_reduction_try4.log`; build completed
successfully (3926 jobs), zero `error:` lines, zero `sorryAx`, and three
standard-axiom audit terminators.

The actual visible-boundary coframe is the finite Schur--polar sum indexed by
`family.visiblePrimes`, multiplied by its exact upper Euler factor. The
selected root convolution distributes over that finite sum. Consequently,
if each actual boundary output, after the same selected root convolution, has
square-summable columns on the named source basis, then the aggregate
`hBoundary` series is summable.

This is a finite-output reduction, not an analytic estimate: the individual
rooted boundary-output square-sums are still open. The actual aggregate
`hBoundary`, unconditional trace limit, signed readback, `qw` sign, C3, and RH
remain open.
