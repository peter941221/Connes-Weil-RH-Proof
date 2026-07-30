# Proof 622: antiresonant interior reverse intertwinement

## Result

Good algebraic reduction, but not a Bone 1 closure.

Let `T` be the actual suffix transition, `R` its reverse, and `B_S` the
complete three-branch boundary response.  Define

```text
K_(p,S) = R^dagger B_S - B_(p::S) R^dagger.
```

Lean proves

```text
Interior_(p,S) = T^dagger K_(p,S).
```

The reason is the correctly ordered scalar identity

```text
T^dagger R^dagger = rho_p I.
```

The corrected radial bracket covariance defect and the suffix-dressing defect
both acquire the same left factor `T^dagger`.  Their inner defects recombine
exactly to `K_(p,S)` before any norm is taken.

## Why this matters

Proof 621 left two provenance channels.  Proof 622 shows that their signed
sum is one reverse-intertwining defect of the actual physical boundary
responses.  The analytic route may now retain this single owner through the
first absolute value.

## Guard

`K_(p,S)` is not the existing local raw defect or its adjoint.  All operators
have the same source-carrier type, so Lean's type checker cannot detect an
illegal left/right swap.

Bone 1, Gate 3U, the finite-S sign, Burnol's identity, and RH remain open.
