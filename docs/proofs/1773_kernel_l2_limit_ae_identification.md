# Proof record 1773: a.e. identification of the L2 and pointwise limits

Date: 2026-09-21

Status: FORMAL, no sign claim.

## Result

`ae_eq_of_lp_tendsto_of_pointwise_tendsto` proves that canonical `MemLp.toLp`
representatives converging in L2 and their raw function representatives
converging pointwise have a.e.-equal limits.

## Route role

This closes the global representative-identification interface for the row
readback.  The remaining construction is to choose the Schwartz approximation,
prove its L2 convergence and pointwise row convergence using records 1771 and
1772, and then apply this theorem to the Plancherel outputs.

## Provenance

Original project formalization using Mathlib's convergence-in-measure
subsequence theorem and a.e. uniqueness of metric limits.  No numerical input,
new axiom, or positivity statement is used.
