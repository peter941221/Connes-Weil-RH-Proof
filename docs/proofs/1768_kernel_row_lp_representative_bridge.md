# Proof record 1768: kernel-row Lp representative bridge

Date: 2026-09-21

Status: FORMAL, no sign claim.

## Result

`sourceKernelRow_integral_eq_toLp_rep` proves that the honest root-kernel row
integral is unchanged when an arbitrary `MemLp` input is replaced by its
canonical `toLp` representative.  The proof is the a.e. representative
identity followed by `integral_congr_ae`.

## Route role

This is the next interface after record 1767.  The Plancherel convolution is
defined on the L2 quotient, whereas the row formula is written on functions.
The theorem removes that representative ambiguity without asserting the still
open arbitrary-L2 Plancherel-to-row equality.  The next analytic obligation is
therefore density/continuity of the row formula itself, followed by its
identification with the bounded Plancherel operator.

## Provenance

This is an original project formalization of the representative bridge.  It
uses the standard Mathlib `MemLp.coeFn_toLp` fact and contains no numerical
input, new axiom, or positivity conclusion.
