# Proof 641: swapped local-pair radial-column bridge

## Result

The result is useful but does not close Bone 1.  Proof 641 identifies the
complete swapped local Hilbert--Schmidt pair cofactor without splitting its
physical branches:

```text
Pair_(p,S).swap.traceProduct * Reverse_(p,S)^dagger
  = LocalRawDefect_(p,S)^dagger * Reverse_(p,S)^dagger
  = -rho_p * K_(p,S),

K_(p,S)
  = Reverse_(p,S)^dagger * BoundaryResponse_S
    - BoundaryResponse_(p::S) * Reverse_(p,S)^dagger.
```

Each `BoundaryResponse` still contains the complete three-branch commutator.
In particular, the reflected second-support and prolate contributions remain
inside the same signed adjacent difference.  The proof takes no separate
Hilbert--Schmidt leg norm.

The cofactor reconstructs the active numerator through the existing exact
Schur identity:

```text
Interior_(p,S)
  = -rho_p^-1 Transition_(p,S)^dagger
      * (Pair_(p,S).swap.traceProduct * Reverse_(p,S)^dagger).
```

## Finite radial-column boundary

Proof 639 constructs only the finite column

```text
C_(p,S,N)
  = (q_p B_0, q_p^2 B_1, ..., q_p^N B_(N-1))
  = Readout_(p,N) * (L_p^dagger newFrame_(p,S)),

||Readout_(p,N)|| <= 32.
```

Proof 641 does not assert that the complete cofactor factors through this
column.  It names the exact extra premise as a bounded map `F_(p,S,N)` with

```text
F_(p,S,N) * C_(p,S,N)
  = Pair_(p,S).swap.traceProduct * Reverse_(p,S)^dagger.
```

Douglas factorization proves that such an `F` of norm at most `M` exists if
and only if the following full-source estimate holds:

```text
||Pair.swap.traceProduct * Reverse^dagger x||^2
  <= M^2 ||C_(p,S,N) x||^2
```

for every source vector `x`.  A basis estimate is insufficient.

The necessary kernel condition is now explicit:

```text
C_(p,S,N) x = 0
  -> Pair.swap.traceProduct * Reverse^dagger x = 0.
```

No current source theorem proves this containment.  The local physical pair
owns trace legality and compactness, but it does not force its complete
coupled cofactor to depend on finitely many radial cells.

## Conditional Bone 1 handoff

If the missing finite-column readout has norm at most `M`, Proof 641 composes
it with Proof 639 before taking a norm and obtains the exact raw-column
readout.  The explicit cost is

```text
||Interior_(p,S) x||
  <= 8 * M * 32 ||L_p^dagger newFrame_(p,S) x||
  = 256 M ||L_p^dagger newFrame_(p,S) x||.
```

Thus a route-uniform bound on these finite-column readouts would be a
sufficient Bone 1 producer.  Proof 641 constructs no such bound and makes no
claim that this stronger finite-column route is necessary.  Bone 1, Gate 3U,
the finite-S sign, Burnol's identity, and RH remain open.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  ...AntiresonantInteriorSwappedLocalPairRadialColumnBridge.lean
ConnesWeilRH/Dev/
  ...AntiresonantInteriorSwappedLocalPairRadialColumnBridgeAudit.lean
```

## Verification

```text
+--------------------------------------+-------+--------+
| target                               | jobs  | result |
+--------------------------------------+-------+--------+
| swapped local-pair bridge source     |  3392 | PASS   |
| focused fifteen-declaration audit    |  3393 | PASS   |
+--------------------------------------+-------+--------+
```

All fifteen audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.
