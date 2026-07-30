# Proof 616: antiresonant exterior adjoint radial factorization

## Result

Proof 616 upgrades Proof 615 from actual suffix-frame columns to the complete
radial subspace. With

```text
E = radialSupportProjection,
F = I - E,
N = normalizedPrimeEulerInverse(p),
X = F N^dagger E,
```

the same readout from Proof 615 satisfies the operator identity

```text
exteriorReadout * ambientLoss^dagger * E = X,
||exteriorReadout|| <= 32.
```

The constant remains independent of the visible prime, suffix list, and
Sonin scale.

## Radial recurrence

The proof first removes the suffix frame from the Proof 612 recurrence. For
every radial input and every `n >= 0`, Lean proves

```text
blockReadout_n * ambientLoss^dagger * E
  = C V^n E,

V = E U_(log p) E,
C = F U_(log p) E.
```

After multiplying by the genuine Euler weights and summing in operator norm,

```text
geometricReadout * ambientLoss^dagger * E = G E.
```

Proof 615's `X=Y G`, together with `X E=X`, then gives the complete radial
factorization.

## Physical consumers

The module proves a generic consequence for every radially supported column
`J`:

```text
E J = J
  => exteriorReadout * ambientLoss^dagger * J = X J.
```

It instantiates this result for both source columns used by the physical
coframe:

```text
J = sourceBandProjection,
J = sourceInclusion.
```

This removes the suffix-frame restriction from the exterior interface. It
does not identify any signed numerator with `X`.

## Verification

```text
focused source build: 3380 jobs, PASS
import-facing audit:  PASS
audited declarations: 9
axioms: [propext, Classical.choice, Quot.sound]

CCM25Concrete aggregate: 3885 jobs, PASS
full repository build:  3966 jobs, PASS
```

## Boundary

Proof 616 is an operator-factorization upgrade only. The metric-coframe Gram
correction, Bone 1, Gate 3U, the finite-S sign, Burnol's identity, and RH
remain open.
