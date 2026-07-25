# Proof 530: physical Schur-Markov alignment

## Result

The normalized physical coframe and response are now connected to the
Schur-Markov owners on the same carriers by exact Lean identities:

```text
normalized coframe
  = (lowerFactor(S) * upperFactor(S)) * mixed Schur-Markov coframe

normalized response
  = (lowerFactor(S) * upperFactor(S)) * Schur-Markov scaled response
```

The source module is
`ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSPhysicalSchurMarkovAlignment.lean`.
The product factor is nonnegative and at most one, by the existing
finite-product theorem `finiteEulerLower_mul_upper_le_one`.

## Why this matters

The two existing uniform ledgers were using different gauges.  The new
identities remove that ambiguity and prove the corresponding norm comparisons
without introducing a new premise or changing operator order.

They also expose the remaining obstruction exactly.  The Schur-Markov scalar
is

```text
rho_S = lowerFactor(S) / upperFactor(S),
```

while the normalized physical response carries `lowerFactor(S)^2`.  The
comparison above multiplies the Schur-Markov response by
`lowerFactor(S) * upperFactor(S)`; it does not divide by `rho_S`.  Therefore
it cannot imply the raw Gate 3U bound.  The missing source theorem remains a
family-uniform bound for the unscaled completed physical response, with the
complete signed endpoint cancellation retained.

## Verification target

The focused audit must report only
`[propext, Classical.choice, Quot.sound]`.  The aggregate import and the full
repository build are required after the source module compiles.
