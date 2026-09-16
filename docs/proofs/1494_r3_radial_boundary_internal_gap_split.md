# 1494 - R3 radial-boundary and internal-gap split

Date: 2026-09-16.

Status: `FORMAL ALGEBRAIC IDENTITY`. No trace-ideal bound or RH conclusion is
claimed.

Consumer: the same-owner healthy-`CompactLog` B5 statement
`0 <= C1SameOwnerWeil.qw g`, through the selected detector-root leakage and
its eventual G8 trace/readback.

## Result

Let `P` be `sourceSoninProjection lambda`, `E` be
`radialSupportProjection lambda`, `J` be `sourceInclusion lambda`, and `B` be
any bounded operator on `finiteSCarrier`. The formal identity is

```text
(I - P) B J = (I - E) B J + (E - P) E B J.
```

The proof uses the projection law `E^2 = E` and the nested-support law
`P E = P`. Lean proves the generic identity and its same-owner specialization
with `B = rootConvolution owner` and the actual source inclusion in
`ConnesWeilRH/Dev/C1G8R3RadialBoundaryGapSplit.lean`:

- `radialSoninComplement_comp_operator_comp_input_eq_boundary_add_gap`;
- `selectedRoot_sourceSoninLeakage_eq_radialBoundary_add_internalGap`.

## Limits

This record gives the formal operator split. The support and translation
identification of its first summand is proved separately in [proof record
1495](1495_r3_radial_boundary_finite_window_identity.md), and [record
1496](1496_r3_radial_boundary_source_energy.md) proves its source-basis
Hilbert--Schmidt energy. No trace-class estimate is claimed for that single
channel. This record also does not estimate the internal prolate gap, prove
`hBoundary`, close the G8 trace/readback, establish detector-specific
semi-local positivity, or prove RH. The remaining analytic targets are those
in [record 1423](1423_r3_radial_boundary_capture_and_prolate_gap.md).

The paired audit prints the axioms for both declarations. Acceptance log:
`0916_r3_radial_gap_split_try2.log` — `Build completed successfully (3211
jobs)`, zero `error:` lines, zero `sorryAx`, and two `Quot.sound]` audit
terminators. Both declarations depend exactly on the standard axiom set
`[propext, Classical.choice, Quot.sound]`.
