# Proof 452: Finite compression trace bridge

## Result

The ordered Hilbert-basis prefix used by Proof 451 has a finite-dimensional
matrix owner.  For a basis `e_i`, an operator `T`, and `N : ℕ`, define the
`Fin N` matrix

```text
M_N(i,j) = ⟪e_i, T e_j⟫.
```

Then

```text
Matrix.trace(M_N)
  = ∑ i ∈ Finset.range N, ⟪e_i, T e_i⟫.
```

This lets a future physical-boundary estimate work with finite compressions
while preserving the exact ordered prefixes consumed by Proof 451.

## Lean interface

The source module is:

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSMovingBandPrefixCompression.lean
```

Its declarations are:

```lean
basisPrefixMatrix
trace_basisPrefixMatrix_eq_rangeDiagonal
trace_basisPrefixMatrix_re_eq_rangeDiagonal_re
ordinaryTraceAlong_norm_le_of_prefixCompressionIntegralBound
canonicalOrdinaryTraceAlong_norm_le_supportRadiusPolynomial_of_prefixCompressionBound
```

The proof only unfolds `Matrix.trace` and uses Mathlib's
`Fin.sum_univ_eq_sum_range`.  No infinite-dimensional trace cyclicity,
compactness, or `N → ∞` assertion is present.

The actual moving-flow consumer accepts the finite-dimensional hypothesis

```text
∀ N,
  |∫_0^1 Re(trace(M_N(actualMovingSoninRootFlow(alpha)))) d alpha| <= C
```

and passes it to Proof 451's ordered-exhaustion theorem.  The fixed-`S`
`IsTraceClassAlong` witness remains a separate premise.

## Boundary

This is an interface bridge, not the Gate 3U producer.  A later theorem must
still provide the signed range-prefix estimate for the actual recombined
moving flow, retain the outer/Sonin/prolate/Gram cancellations, and separately
prove fixed-`S` trace legality.  Gate 3U, the finite-`S` sign, Burnol's
identity, and `_root_.RiemannHypothesis` remain open.
