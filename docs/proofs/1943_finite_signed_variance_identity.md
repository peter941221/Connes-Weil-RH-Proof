# 1943 — Exact finite signed-variance identity

Date: 2026-09-24

## Result

`ConnesWeilRH.Source.C1SignedVarianceIdentity.finite_signed_variance_identity`
formalizes the exact finite identity used by the four-point span gate. For
finite weights `c` and profile values `p`, the determinant of the zeroth,
first, and second weighted moments equals one half of the double sum of
weighted squared pairwise differences.

The theorem allows signed weights. Therefore it is an algebraic reduction,
not a positivity theorem: the pairwise sum has no fixed sign until the actual
physical kernel supplies a signed-measure estimate.

## Route impact

This removes the need to manipulate the three gate entries independently at
the algebraic layer. The remaining live obligation is an actual-owner
pairwise physical-kernel budget for the four-point span, with the finite
visible-prime set and erased remainder retained. It does not prove the gate
determinant is negative and does not advance an RH claim by itself.

## Verification

```text
20260924_variance_identity36.log: Build completed successfully (3810 jobs).
20260924_variance_identity_audit.log: Build completed successfully (3811 jobs).
axioms: [propext, Classical.choice, Quot.sound]
sorryAx: none
```

The proof is finite algebra plus finite-sum reindexing; no numerical input is
used.
