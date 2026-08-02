# Proof 740: Gate Physical Prefix Boundary Kernel Pairing

## Result

Proof 740 reads Proof 739's centered common-boundary trace as a finite sum of
complete physical-pair coefficients and opens the outer/reflected coordinate
to the genuine compact-root signed kernel.

Write

```text
J   = sourceInclusion,
U_S = sourceEndpointCancellationResidual,
F_S = sourceActualBandForwardCoframe.
```

For one source vector `x`, Lean proves

```text
<x, GateResponse_S x>
  = PhysicalPair(Jx,U_S x) - PhysicalPair(F_S x,Jx).
```

Each complete physical pair has the exact decomposition

```text
PhysicalPair(x,y)
  = OuterSignedKernel(x,y)
    + SecondSupportProlateRemainder(x,y).
```

The first summand is the two-sided response of the existing skew-adjoint
compact-root operator

```text
P^dagger N - N^dagger P.
```

The second-support and prolate coordinates remain coupled.  Consequently,
Proof 739's trace is exactly

```text
sum_(i < N) [
  OuterSignedKernel(J e_i,U_S e_i)
    + SecondSupportProlateRemainder(J e_i,U_S e_i)
  - OuterSignedKernel(F_S e_i,J e_i)
    - SecondSupportProlateRemainder(F_S e_i,J e_i)
].
```

The consumer accepts a common bound for this one ordered prefix scalar.

## Why This Matters

The outer compact-root kernel is now visible before any absolute value:

```text
centered boundary trace
        |
        | exact finite diagonal readout
        v
complete physical-pair difference
        |
        | open only the outer/reflected coordinate
        v
outer signed compact kernel + coupled second-support/prolate remainder
        |
        | retain one signed prefix
        v
active Gate 3U estimate
```

This is an exact normal form, not an estimate.  Its purpose is to expose the
real compact-support geometry while preserving the cancellation with the
second-support and prolate terms.

## Guard

Do not estimate the outer kernel separately from the coupled remainder.  Do
not estimate the `(J,U_S)` and `(F_S,J)` orientations separately.  The source
prefix projection must remain between the family-dependent coframes and the
source adjoint legs; Proof 740 does not justify moving it through either
factor.

Proof 740 proves no bound uniform in `S` or `N`.  Gate 3U, the finite-S sign,
Burnol's identity, and `_root_.RiemannHypothesis` remain open.

## Verification

The Windows source of truth was synchronized to the Ubuntu-24.04 WSL2 ext4
mirror.  The focused Proof 740 source and audit passed with `3384/3384` jobs,
the `CCM25Concrete` aggregate with `4008/4008`, and the full repository with
`4089/4089`.

All seven audited Proof 740 theorems use exactly
`[propext, Classical.choice, Quot.sound]`.  The source has no `sorry`,
`admit`, user axiom, heartbeat increase, recursion-limit increase, overlong
line, or new linter warning.
