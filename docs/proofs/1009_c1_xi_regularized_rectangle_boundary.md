# 1009 Finite Xi Regularized Rectangle Boundary

Date: 2026-08-14

## Result

The finite-factor Gate 2 contour chain now has a legal rectangular boundary
interface. The new module is:

```text
ConnesWeilRH/Dev/C1XiFiniteRectangleBoundary.lean
```

It defines one oriented four-edge functional:

```text
xiRectangleBoundaryIntegral(f, z, w)
  = bottom(f) - top(f) + I * right(f) - I * left(f)
```

and proves the following replacement theorem:

```text
xiRectangleBoundaryIntegral(xiContourKernel F, z, w)
  = xiRectangleBoundaryIntegral(xiClosedBallPrincipalKernel F c R, z, w)
```

under one finite-factor owner, full rectangle containment in its open
factorization ball, and explicit xi-nonvanishing on all four boundary edges.

## Why This Is Legal

```text
xiContourKernel on a zero-free boundary
        |
        | pointwise finite-factor identity
        v
finite principal part + regularized remainder
        |
        | interval-integral congruence on each of four edges
        v
B(xiContourKernel) = B(principal) + B(regularized)
        |
        | Cauchy-Goursat only for the differentiable remainder
        v
B(xiContourKernel) = B(principal)
```

The proof deliberately does not pass `xiContourKernel` to rectangular Cauchy:
it has poles at xi zeros in the rectangle interior. Instead,
`xiClosedBallRegularizedKernel` is differentiable throughout the owning open
ball, so the existing theorem
`integral_boundary_rect_eq_zero_of_rectangle_subset_xiBall` applies only to
that remainder.

An interior zero is permitted. It belongs to the finite principal part. The
new boundary predicate excludes zeros only on the integration path:

```text
xiRectangleBoundaryAvoidsZeros z w
  = bottom edge nonzero
  AND top edge nonzero
  AND right edge nonzero
  AND left edge nonzero
```

This preserves the same finite divisor owner from the factorization through
the boundary replacement.

## Evidence

The isolated WSL2 ext4 verification command was:

```text
flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build ConnesWeilRH.Dev.C1XiFiniteRectangleBoundaryProbe
```

It completed successfully with `3527` jobs. The focused import-facing audit
reported the following axioms for both public declarations:

```text
[propext, Classical.choice, Quot.sound]
```

There is no `sorryAx`, `sorry`, `admit`, or project axiom in the new module.
The rectangle Cauchy source is mathlib:

```text
Mathlib/Analysis/Complex/CauchyIntegral.lean
Complex.integral_boundary_rect_eq_zero_of_differentiableOn
```

It is used through the already-owned
`C1XiFiniteRegularizationCauchy` interface.

## Boundary

This does not compute the principal-part boundary integral. The necessary next
theorem is a finite rectangle-residue readout:

```text
B(xiClosedBallPrincipalKernel F c R, z, w)
  = -2*pi*i * sum of factor-owned residues strictly inside the rectangle
```

That theorem must distinguish interior, exterior, and boundary divisor
points. The circle readout in `C1XiFiniteCommonCircle` cannot be substituted
for it: a circle and a rectangle have different contours, and no geometric
equivalence has been formalized.

No contour limit, arithmetic-side readback, Gate 2 explicit-formula equality,
or Riemann Hypothesis claim is made here.

Reference for the intended explicit-formula contour architecture:

```text
Jean-Francois Burnol, The Explicit Formula in Simple Terms,
https://arxiv.org/pdf/math/9810169, pp. 3-4.
```
