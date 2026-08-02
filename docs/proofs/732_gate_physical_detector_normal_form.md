# Proof 732: Gate Physical Detector Normal Form

## Result

Proof 732 removes the three-branch commutator notation from the centered Gate
owner on the source Sonin carrier.

Let

```text
J   = sourceInclusion,
R   = J J^dagger,
W   = detectorOperator,
K   = [R,W],
F_S = sourceActualBandForwardCoframe,
U_S = sourceEndpointCancellationResidual.
```

Proof 729 gives

```text
GateResponse_S = J^dagger K D_S - F_S^dagger K J,
D_S = J + U_S.
```

The source and coframe range identities are

```text
RJ = J,                  J^dagger R = J^dagger,
R U_S = 0,               R F_S = 0.
```

Hence the fixed source block cancels and the commutator acts only across its
two off-diagonal corners:

```text
GateResponse_S
  = J^dagger W U_S + F_S^dagger W J.
```

Lean proves this as equality of operators, not only equality of ordinary
traces. The implementation expands the adjoint of Proof 727's complete
boundary moment and uses the genuine self-adjoint detector theorem
`detectorOperator_isSelfAdjoint`.

The complete ownership chain is now

```text
               source operator
                     |
                     v
J^dagger W U_S + F_S^dagger W J
                     |
                     | exact operator equality
                     v
             GateResponse_S
                     |
                     | Proof 731 legal HS cycle
                     v
Tr_boundary(right C_S^0 left^dagger).
```

Trace legality, ordinary trace, and every scalar trace-norm upper bound transfer
exactly to the detector off-diagonal owner. Lean also proves that its source
trace equals Proof 731's centered common-boundary trace.

## Why This Matters

All detector dependence is now the actual compact-root convolution square
`W`; the auxiliary commutator expansion no longer obscures where compact
support must act. Both family-dependent coordinates remain inside one signed
operator:

```text
endpoint-residual crossing  +  reverse-forward crossing.
```

This is the correct next input for a detector-specific estimate. Estimating
the two terms separately would lose the cancellation that Gate 3U requires.

## Guard

Proof 732 is an exact normal form, not a uniform estimate. It does not show
that either coordinate is trace class separately, and it does not authorize
separate trace-norm bounds. Gate 3U, the finite-S sign, Burnol's identity, and
`_root_.RiemannHypothesis` remain open.

## Verification

The Windows source of truth was synchronized to the Ubuntu-24.04 WSL2 ext4
mirror and built under the shared Lake lock.

```text
source/audit/aggregate      4001/4001  PASS
final full acceptance       4083/4083  PASS
```

Every audited theorem uses exactly
`[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, user axiom,
heartbeat increase, recursion-limit increase, or new linter warning was added.
