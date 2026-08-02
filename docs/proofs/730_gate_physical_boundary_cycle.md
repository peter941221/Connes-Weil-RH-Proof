# Proof 730: Gate Physical Boundary Cycle

## Result

Proof 730 performs the legal rectangular trace cycle that Proof 729 exposes.
Let

```text
J = sourceInclusion,
D = sourceActualBandForwardEndpointCoframe,
F = sourceActualBandForwardCoframe.
```

The complete ambient coframe difference is

```text
C_S = D o J^dagger - J o F^dagger.
```

Let `left` and `right` be the existing common Hilbert--Schmidt factors of the
genuine three-branch Sonin detector commutator.  Lean constructs the one
boundary-carrier operator

```text
BoundaryCycle_S = right o C_S o left^dagger
```

and proves

```text
Tr_source(GateResponse_S) = Tr_boundary(BoundaryCycle_S).
```

The mechanism is exact:

```text
Tr_source(J^dagger K D - F^dagger K J)
                 |
                 | two Hilbert-Schmidt cycles
                 v
Tr_boundary(
  right (D J^dagger - J F^dagger) left^dagger).
```

Both cycles use the same common compact-root factorization of `K`.  Lean also
proves trace legality of the recombined boundary operator and a bidirectional
transfer for every scalar trace-norm bound.

## Why This Matters

The family-dependent endpoint and forward coframes are no longer fed into
separate norm estimates.  Their signed difference is formed first, between
the two fixed compact-root boundary factors.  This is the correct carrier on
which compact support can interact with the complete cancellation before an
absolute value is taken.

Proof 730 does not estimate `BoundaryCycle_S`; Gate 3U, the uniform-in-S
bound, the finite-S sign, Burnol's identity, and RH remain open.

## Verification

The Windows source of truth was synchronized to the Ubuntu-24.04 WSL2 ext4
mirror and checked under the shared Lake lock.  The focused source target
passed with `3353/3353` jobs.  The joint Proof 729/730 source, import-facing
audit, and `CCM25Concrete` aggregate batch passed with `4000/4000` jobs.  The
full repository passed with `4079/4079` jobs.

All four audited Proof 730 theorems use exactly
`[propext, Classical.choice, Quot.sound]`.  No `sorry`, `admit`, user axiom,
heartbeat increase, recursion-limit increase, or new linter warning was
added.
