# 1925 — Route A exact aggregate/residual reduction

Date: 2026-09-24.

Status: formal reduction. The final signed margin and RH remain open.

## Result

For every actual `OrbitG8Geometry`, the new theorem
`intervalIntegral_orbitFinitePhysicalKernelIntegrand_eq_actualResidual`
proves:

```text
integral(actual finite physical-kernel aggregate)
  = integral(actual coboundary residual).
```

The proof uses the primitive `Q(t) = t * actualAggregate(t)`, its already
proved zero endpoint values, and the exact derivative identity. Continuity and
interval integrability of the actual grouped derivative aggregate are proved
in the same leaf.

## Why this is a real reduction

The previous Round-2 target was phrased using
`-t * actualAggregateDerivative(t)`. The new theorem removes that derivative
from the quantitative target entirely. It also keeps the finite visible-prime
sum grouped, so no primewise absolute majorant or cancellation-destroying
replacement is introduced.

The remaining target is precisely:

```text
archimedeanTerm(square) + integral(actualAggregate) <= -epsilon,
epsilon > 0.
```

This is smaller than the prior API obligation: the derivative residual is no
longer an independent function whose integral must be controlled. It is still
an analytic signed-integral inequality, not yet a proof of nonnegativity or RH.

## Verification

Focused build:

```text
20260924_direct_coboundary_reduction6.log
Build completed successfully (3791 jobs)
```

The paired audit prints only `[propext, Classical.choice, Quot.sound]` for all
three declarations, with no `sorryAx`.
