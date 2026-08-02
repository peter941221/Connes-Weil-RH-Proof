# Proof 733: Gate Physical Signed Diagonal

## Result

Proof 733 converts the detector-only Gate owner from Proof 732 into its exact
pointwise signed diagonal without splitting the infinite ordinary trace.

Let

```text
J   = sourceInclusion,
W   = detectorOperator,
F_S = sourceActualBandForwardCoframe,
P_S = sourcePhysicalCoframeLeakage,
U_S = sourceEndpointCancellationResidual = F_S + P_S.
```

The source operator has the algebraic decomposition

```text
J^dagger W U_S + F_S^dagger W J
  = (J^dagger W F_S + F_S^dagger W J)
    + J^dagger W P_S.
```

The bracketed forward owner is self-adjoint. For every source Sonin vector
`x`, its two diagonal terms are complex conjugates, so Lean proves

```text
<x, GateResponse_S x>
  = 2 Re <Jx, W(F_S x)> + <Jx, W(P_S x)>.
```

The same theorem is proved for the literal lower-factor-gauged Gate response,
not only for the named Proof 732 owner. Consequently,

```text
Im <x, GateResponse_S x>
  = Im <Jx, W(P_S x)>.
```

The structure is now explicit:

```text
                       Gate diagonal
                            |
              +-------------+-------------+
              |                           |
              v                           v
  forward conjugate pair        complete physical leakage
      2 Re <Jx,W F_Sx>               <Jx,W P_Sx>
        purely real                  retains all branches
```

## Why This Matters

The forward coordinate is no longer an arbitrary complex contribution; it is
one real covariance counted with its adjoint. Every non-real diagonal term is
forced into the complete outer/second-support/prolate leakage crossing. This
identifies the exact signed scalar that a detector-specific estimate must
control.

## Trace-Legality Guard

Proof 733 deliberately proves no theorem of the form

```text
Tr(A+B) = Tr(A) + Tr(B).
```

Proof 732 proves only that the complete sum is trace legal. Neither the
forward symmetric owner nor the physical leakage crossing is asserted to be
trace class separately. The pointwise identity may be summed only after a new
producer proves the required separate summability or supplies a signed
finite-partial-sum argument that keeps both terms together.

Gate 3U, the finite-S sign, Burnol's identity, and
`_root_.RiemannHypothesis` remain open.

## Verification

The Windows source of truth was synchronized to the Ubuntu-24.04 WSL2 ext4
mirror and built under the shared Lake lock.

```text
source/audit/aggregate      4002/4002  PASS
final full acceptance       4083/4083  PASS
```

Every audited theorem uses exactly
`[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, user axiom,
heartbeat increase, recursion-limit increase, or new linter warning was added.
