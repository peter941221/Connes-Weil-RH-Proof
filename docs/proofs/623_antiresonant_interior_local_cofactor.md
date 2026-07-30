# Proof 623: antiresonant interior local cofactor

## Result

The exact relationship with the existing local raw owner is now closed.

Write

```text
A = rawIntertwiningDefect
L = localRawDefect
G = rawPhysicalFourTermRow = A^dagger
I = Interior
K = reverse-intertwining defect from Proof 622.
```

Lean proves the noncommutative ledger

```text
I       = G R^dagger
I^dagger = R A
L       = -A R
K T^dagger = -L^dagger

I^dagger + L = R A - A R.
```

Thus `I^dagger` is not `-L`; their difference is the genuine commutator
`[R,A]`.  The two-sided cofactor is

```text
T^dagger L^dagger R^dagger = -rho_p I,
I = -rho_p^(-1) T^dagger L^dagger R^dagger.
```

## Why this matters

The old response-facing producer can be reused only with both Schur factors
in their proved order.  A one-sided transfer would silently commute `R` and
`A` and target the wrong operator.

## Guard

This is an exact coordinate bridge.  It does not construct a bounded factor
through `oldCarrierAnalysis`, and fixed-S trace-class information for `L`
does not imply the required family-uniform Douglas factorization.
