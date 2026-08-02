# Proof 727: Endpoint Residual Boundary-Moment Bridge

## Result

Proof 727 inserts the named Proof 726 residual into the existing raw physical
boundary moment. The complete signed owner is

```text
sourceEndpointCancellationBoundaryMoment
  = residual^dagger o detector o sourceInclusion
    + sourceInclusion^dagger o detector o sourceActualBandForwardCoframe.
```

Lean proves that this is exactly the existing family-indexed raw coframe
boundary moment. After the literal visible-prime suffix alignment, it reads
back to the existing finite-S remainder response:

```text
sourceEndpointCancellationBoundaryMoment
  = sourceActualBandFiniteEulerRemainderResponse^dagger.
```

Therefore trace legality transfers from the remainder response, and the
ordinary trace has the exact adjoint orientation:

```text
Tr(boundaryMoment) = star(Tr(remainderResponse)).
```

This closes an ownership mismatch only. The residual is one coordinate of a
complete signed moment; the forward coordinate remains even if the residual
vanishes. Consequently Proof 727 does not justify a residual-only
factorization or zero claim, and it does not prove Gate 3U, the finite-S sign,
Burnol's identity, or RH.

## Verification

The Windows source of truth was synchronized to the Ubuntu-24.04 WSL2 ext4
mirror. The focused source, import-facing audit, and aggregate were built in
one batch under the shared Lake lock, followed by the full repository build.

```text
+----------------------------------+-------+--------+
| target                           | jobs  | result |
+----------------------------------+-------+--------+
| source + audit + aggregate batch | 3996  | PASS   |
| full repository                  | 4076  | PASS   |
+----------------------------------+-------+--------+
```

All six audited theorems use exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, user axiom, heartbeat increase, or recursion-limit
increase was added.
