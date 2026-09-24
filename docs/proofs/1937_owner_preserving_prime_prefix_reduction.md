# Record 1937: owner-preserving prime-prefix reduction

Date: 2026-09-24.

## Exact result

The selected `OrbitG8Geometry` owner has a finite visible prime-power set.
For any `CompactLogTest F` and any member `n` of its actual
`globalPrimeIndexSet F`, the exact identity is

```text
finitePrimeSum F
  = finitePrimeTerm F n
    + sum over (globalPrimeIndexSet F).erase n of finitePrimeTerm F
```

If `n` is not visible, its real finite-prime term is exactly zero. The paired
Lean audit `C1FourPointPrimePrefixReductionAudit.lean` builds successfully and
prints only the standard three axioms; no `sorryAx` occurs.

## Why this matters for Cut 2

The 1936 probe suggested using `n = 2` as the first finite certificate term.
The actual owner cutoff theorem proves only that all visible indices lie in a
finite range. It does not prove that `2` is visible, which additionally
requires the owner-specific complex prime term at `2` to be nonzero. An
ambient-bump visibility result cannot be transferred to the selected owner.

The live obligation is therefore explicit and exhaustive:

1. prove `2` visible for the selected owner and estimate the exact remainder;
2. prove a different owner-specific visible index and use it as the prefix;
3. abandon the single-prefix certificate if neither can supply the strict
   determinant margin.

The same leaf also proves a stronger owner-specific decomposition: after
rewriting through the actual `OrbitG8Geometry` finite range, the range can be
split at `n = 2` without assuming that `2` belongs to the visible set. The
fixed term is then automatically zero in the non-visible case. This removes
the visibility premise from the algebraic prefix split; only the eventual
strict sign estimate remains.

This record is a formal algebraic reduction, not a determinant sign proof and
not an RH claim.

Classification: FORMAL exact reduction.
