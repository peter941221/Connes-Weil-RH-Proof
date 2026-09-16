# 1496 - R3 radial-boundary source-basis energy

Date: 2026-09-16.

Status: `FORMAL HILBERT--SCHMIDT ENERGY FOR THE RADIAL BOUNDARY CHANNEL`.
This is one channel of the selected-root source leakage; it is not a full
trace-class or G8 readback result.

Consumer: the same-owner healthy-`CompactLog` B5 statement
`0 <= C1SameOwnerWeil.qw g`, through the selected detector-root leakage
decomposition and its eventual G8 trace/readback.

## Result

For any selected square owner, the continuous compact-output kernel on its
finite input and output windows has square-summable columns on every named
input Hilbert basis. The theorem
`selectedRootBoundaryWindowOperator_basis_normSq_summable` transfers that
kernel estimate through the finite-window restriction, positive-half-line
projection, and zero extension, proving the zero-boundary crossing operator
is Hilbert--Schmidt on the ambient logarithmic carrier.

The theorem
`selectedRoot_radialBoundary_sourceBasis_normSq_summable` then transfers the
same estimate through the actual radial translation and source inclusion. For
every selected scale and every named basis of `sourceSoninCarrier lambda`,
the actual radial boundary output columns have a summable squared-norm family:

```text
Summable i =>
  norm(((I - radialSupportProjection lambda)
    * rootConvolution owner * sourceInclusion lambda)(sourceBasis i))^2.
```

The proof uses the existing continuous-kernel basis estimate and the general
bounded precomposition/postcomposition lemmas in `HilbertSchmidtIdeal.lean`.
The paired audit is in
`ConnesWeilRH/Dev/C1G8R3RadialBoundaryEnergyAudit.lean`.

## Limits

This closes the Hilbert--Schmidt energy of the radial-boundary summand in
record 1494. It does not bound the internal radial-but-non-Sonin prolate gap,
which is still needed for the full source leakage. It also does not estimate
the separate finite visible-prime boundary outputs in the G8 metric
coframe, identify the G8 trace limit with `qw`, prove detector-specific
semi-local positivity, close C3, or prove RH. No trace-class claim is made for
this single HS channel by itself.

Acceptance log: `0916_r3_boundary_energy_try4.log` —
`Build completed successfully (3212 jobs)`, zero `error:` lines, zero
`sorryAx`, and two `Quot.sound]` audit terminators. Both declarations depend
exactly on `[propext, Classical.choice, Quot.sound]`.
