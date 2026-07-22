# Proof 492: Raw remainder common physical pair

Date: 2026-07-22

## Result

The result is structurally good, but Gate 3U remains open.  The raw actual-band
remainder now has one Hilbert--Schmidt pair in which the forward first jet and
the raw Gram endpoint share a right leg before energy is taken.

Write

```text
T =cc20ThreeBranchCommutator,
J =sourceInclusion,
V_S=B A_S J,
C_S=H_S J G_S^-1.
```

Here `A_S` is the normalized causal inverse and `C_S` is the raw metric
coframe.  Lean proves the exact operator identity

```text
raw remainder=J^dagger T(V_S+C_S)-V_S^dagger T J.
```

If the existing physical pair has legs `L,M`, so that `T=L^dagger M`, the new
pair has the two coordinates

```text
left  =(L J,       L V_S),
right =(M(V_S+C_S), -M J).
```

Its trace product is exactly

```text
sourceActualBandFiniteEulerRemainderResponse
  =lowerFactorGaugedActualBandCompletedRelativeResponse.
```

## Why this changes the estimator

The old legal owner was an orthogonal direct sum:

```text
+----------------------+----------------------+----------------------+
| forward first jet    | reverse first jet    | raw endpoint         |
+----------------------+----------------------+----------------------+
| left  =L J           | left  =L V_S         | left  =L J           |
| right =M V_S         | right =-M J          | right =M C_S         |
+----------------------+----------------------+----------------------+
```

The first and third columns have the same left leg.  Treating them as
orthogonal coordinates changes their right energy into

```text
norm(M V_S)^2+norm(M C_S)^2,
```

which cannot retain cancellation between the normalized first jet and the raw
coframe.  Proof 492 uses `addOfLeftEq` to form the right leg

```text
M V_S+M C_S=M(V_S+C_S)
```

first.  Its energy is therefore

```text
norm(M(V_S+C_S))^2.
```

This is an exact change of Hilbert--Schmidt owner, not a triangle-inequality
estimate.

```text
 old legality owner                  Proof 492 owner

 (LJ,MV) ----+                       (LJ,M(V+C))
              +-- orthogonal sum          |
 (LJ,MC) ----+                            +-- cancellation is still visible

 (LV,-MJ) -------------------------- (LV,-MJ)
```

## Lean ownership

The source and audit are

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSRawRemainderCommonPair.lean

ConnesWeilRH/Dev/
  CCM24FiniteSRawRemainderCommonPairAudit.lean
```

The generic helper `boundedPrecompAddRight` proves that two bounded
precompositions with a common left map have one combined right leg.  The
actual-carrier layer then proves:

```text
sourceActualBandFiniteEulerPairedResponse_eq_threeBranch
sourceActualBandFiniteEulerSoninResponse_eq_commonPhysicalFirstJet
sourceBandGramResponse_eq_neg_commonPhysicalEndpoint
sourceActualBandRawRemainderCommonPhysicalResponse_eq_remainder
sourceActualBandRawRemainderCommonPairData_traceProduct_eq_gauged.
```

The theorem `sourceActualBandForwardEndpointPairData_right_apply` exposes the
combined leg pointwise.  This prevents a later consumer from silently
replacing it by two independent energies.

## Verification

The acceptance batch ran in the Ubuntu 24.04 ext4 verification environment
with the existing Lake cache.

```text
+--------------------------------------+-------+--------+
| target                               | jobs  | result |
+--------------------------------------+-------+--------+
| Proof 492 focused axiom audit        |  3274 | PASS   |
| CCM25Concrete aggregate              |  3766 | PASS   |
| full repository                      |  3847 | PASS   |
+--------------------------------------+-------+--------+
```

The generic ring theorem uses exactly `[propext]`.  The other twenty audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`.  The new
source and audit add no `sorry`, `admit`, or axiom declaration and emit no new
linter warning.

## Boundary

Proof 492 does not prove that `V_S+C_S` is contractive, and it does not bound
that raw operator in isolation.  The next valid analytic target is narrower:

```text
sum_i norm(M((V_S+C_S)e_i))^2
  <= support--Sobolev polynomial independent of S.
```

The complete physical leg `M`, the coframe sum, and compact-root support must
remain together until this estimate is proved.  Splitting the sum back into
`M V_S` and `M C_S`, or estimating `C_S` by its operator norm, recreates the
inverse lower-factor-square loss from Proof 489.

Gate 3U, the finite-S sign, negative-owner integration, Burnol's identity, and
RH remain open.
