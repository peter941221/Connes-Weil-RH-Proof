# 1445 — R3 scalar reverse-endpoint socket

**Date:** 2026-09-14.

**Status:** FORMAL / GREEN.

**Consumer:** the healthy-`CompactLog`, B5-shaped same-owner conclusion
`0 <= C1SameOwnerWeil.qw g`, through the R3 alternating-power endpoint.

## Result

The scalar endpoint now has a precise reverse-side consumer. If the squared
norms of the alternating powers converge to the squared norm of the
intersection projection, then uniqueness of the scalar limit and
nonnegativity imply

```text
ciInf_n ||T_b^n v|| <= ||r_b v||.
```

Together with record 1444, this gives the full scalar equality and therefore
the zero-distance/strong-convergence consumer. The remaining analytic input is
exactly the squared-norm exhaustion statement; it is not hidden in a spectral
gap or a projection algebra identity.

## Formal declaration

`doubledShiftAlternatingProduct_ciInf_norm_le_projection_of_sq_tendsto`

## Acceptance

The focused audit build log
[`025_scalar_reverse_socket_try1.log`](/home/peter/rh/build-logs/025_scalar_reverse_socket_try1.log)
reports `Build completed successfully (3178 jobs)`, zero `error:` lines,
zero `sorryAx`, and forty-one standard `Quot.sound` entries.
