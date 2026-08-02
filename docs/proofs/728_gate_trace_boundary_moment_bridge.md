# Proof 728: Gate-Trace Boundary-Moment Bridge

## Result

Proof 728 identifies the Gate-facing lower-factor-gauged response with the
complete signed boundary moment from Proof 727.  The two operators have the
exact adjoint relation

```text
boundaryMoment = GateResponse^dagger
GateResponse = boundaryMoment^dagger.
```

Here `GateResponse` abbreviates the existing Lean object
`lowerFactorGaugedActualBandCompletedRelativeResponse`; no new response owner
is introduced.

The relationship is a direct same-object chain:

```text
boundaryMoment
    |
    | Proof 727
    v
sourceActualBandFiniteEulerRemainderResponse^dagger
    ^
    | existing lower-factor gauge identity
    |
GateResponse^dagger
```

Consequently Lean proves, for every Hilbert basis,

```text
Tr(boundaryMoment) = star(Tr(GateResponse))
Tr(GateResponse) = star(Tr(boundaryMoment))

norm(Tr(GateResponse)) = norm(Tr(boundaryMoment)).
```

Trace legality is equivalent in the two orientations, and every real scalar
upper bound on the trace norm transfers in both directions.  No trace cycle
and no real-trace premise is used.

## Meaning

This closes the remaining ownership mismatch at the Gate 3U interface.  The
next analytic theorem may work directly with the complete signed physical
boundary moment

```text
residual^dagger o detector o sourceInclusion
  + sourceInclusion^dagger o detector o forward
```

and its bound will be literally equivalent to the existing Gate-facing trace
bound.  Both signed coordinates still have to remain together before taking
an absolute value.  Proof 728 supplies no uniform bound, cancellation, finite-S
sign, Burnol identity, or RH proof.

## Verification

The Windows source of truth was synchronized to the Ubuntu-24.04 WSL2 ext4
mirror and byte-checked with SHA-256.  The focused source, import-facing audit,
and aggregate were built in one batch under the shared Lake lock, followed by
the full repository build.

```text
+----------------------------------+-------+--------+
| target                           | jobs  | result |
+----------------------------------+-------+--------+
| source + audit + aggregate batch |  3997 | PASS   |
| full repository                  |  4077 | PASS   |
+----------------------------------+-------+--------+
```

All seven audited theorems use exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, user axiom, heartbeat increase, recursion-limit increase,
or new linter warning was added.
