# 1495 - R3 radial-boundary finite-window identity

Date: 2026-09-16.

Status: `FORMAL SUPPORT / TRANSLATION IDENTITIES`. No trace-ideal estimate or
RH conclusion is claimed.

Consumer: the same-owner healthy-`CompactLog` B5 statement
`0 <= C1SameOwnerWeil.qw g`, through the selected detector-root boundary
channel and its eventual G8 trace/readback.

## Result

For a selected square owner, compactness of its source test gives an actual
support radius `R`. The zero-boundary crossing of the selected root convolution
from the positive half-line to the negative half-line is exactly the zero
extension of the existing compact-output root factor on `[-R, 0]`:

```text
selectedRootBoundaryWindowOperator owner
  = (I - cc20PositiveHalfLineProjection)
      * rootConvolution owner
      * cc20PositiveHalfLineProjection.
```

The actual CCM24 radial source leakage is then exactly this same finite-window
operator translated to the scale `lambda`, with the actual source inclusion
transported on its input:

```text
(I - radialSupportProjection lambda)
  * rootConvolution owner * sourceInclusion lambda
= T(-log lambda) * selectedRootBoundaryWindowOperator owner
  * T(log lambda) * sourceInclusion lambda.
```

Both identities are formal in
`ConnesWeilRH/Dev/C1G8R3RadialBoundarySupportIdentity.lean`:

- `selectedRoot_zeroBoundaryCrossing_eq_finiteWindow`;
- `selectedRoot_radialSourceLeakage_eq_translatedFiniteWindow`.

The first proof identifies the half-line crossing using the compact support of
the selected root kernel and the existing compact-output factor. The second
uses the exact translation conjugacy for the radial projection, translation
covariance of root convolution, and the fact that the source inclusion lands
in the Sonin subspace fixed by the radial projection.

## Limits

This record proves exact support and transport identities only. Proof record
1496 separately proves square-summability of the translated radial-boundary
outputs on any named source basis. Neither record estimates the internal
prolate-gap channel from record 1494 or the distinct finite visible-prime G8
boundary coframe outputs. The selected support radius depends on the owner.
The G8 diagonal root energies, full trace/readback, detector-specific
semi-local positivity, C3, and RH therefore remain open. The binding route and
its healthy-`CompactLog` B5 consumer are unchanged.

The paired audit prints both theorem declarations. Acceptance log:
`0916_r3_boundary_support_try13.log` — `Build completed successfully (3211
jobs)`, zero `error:` lines, zero `sorryAx`, and two `Quot.sound]` audit
terminators. Both declarations depend exactly on
`[propext, Classical.choice, Quot.sound]`.
