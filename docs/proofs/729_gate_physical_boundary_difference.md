# Proof 729: Gate Physical Boundary Difference

## Result

Proof 729 replaces the abstract Gate remainder by the actual compact-root
physical boundary owner already defined as
`sourceActualBandRawRemainderCommonPhysicalResponse`.  Write

```text
J = sourceInclusion,
K = cc20ThreeBranchCommutator(E, Q, K_prol, detector),
D = sourceActualBandForwardEndpointCoframe,
F = sourceActualBandForwardCoframe.
```

Lean proves the exact same-object identity

```text
lowerFactorGaugedActualBandCompletedRelativeResponse
  = J^dagger o K o D - F^dagger o K o J.
```

The proof is the following direct chain:

```text
Gate response
    |
    | Proof 728
    v
boundaryMoment^dagger
    |
    | existing physical-owner theorem
    v
J^dagger o K o D - F^dagger o K o J.
```

The middle operator is not an abstract commutator.  The existing identity

```text
K = [sourceSoninProjection, detector]
```

realizes it as the completed outer, second-support, reflected-outer, and
prolate compact-root ledger.  Both endpoint/forward coordinates remain inside
one subtraction.  Proof 729 deliberately reuses this existing owner instead
of introducing a duplicate definition.

## Consequence

For every source Hilbert basis, trace legality and every scalar trace-norm
upper bound are equivalent between the Gate response and this complete
physical boundary difference.  No trace cycle, conjugation, branchwise norm,
or real-trace premise remains at this interface.

This is still an ownership theorem, not the uniform estimate.  The next
analytic step must use compact root support on `K` before taking the absolute
value of the complete signed trace.  Proof 729 does not prove Gate 3U, the
finite-S sign, Burnol's identity, or RH.

## Verification

The Windows source of truth was synchronized to the Ubuntu-24.04 WSL2 ext4
mirror and checked under the shared Lake lock.  The joint Proof 729/730
source, import-facing audit, and `CCM25Concrete` aggregate batch passed with
`4000/4000` jobs.  The full repository passed with `4079/4079` jobs.

All six audited Proof 729 declarations use exactly
`[propext, Classical.choice, Quot.sound]`.  No `sorry`, `admit`, user axiom,
heartbeat increase, recursion-limit increase, or new linter warning was
added.
