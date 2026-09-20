# Proof record 1770: dense-core uniqueness of the L2 root operator

Date: 2026-09-21

Status: FORMAL, no sign claim.

## Result

`rootConvolution_eq_of_schwartz_core` proves that a continuous L2 operator
which agrees with the Plancherel root convolution on every Schwartz
`toLp` input agrees with it on the full L2 carrier.

## Route role

This isolates the final operator-identification step for the row readback.
The remaining analytic task is now sharply typed: construct a continuous L2
operator from the honest row integral and prove its Schwartz-core formula.
The theorem itself does not provide that operator, and it makes no positivity
claim.

## Provenance

Original project formalization using Mathlib's Schwartz `toLp` dense-range
theorem.  No numerical input or new axiom is used.
