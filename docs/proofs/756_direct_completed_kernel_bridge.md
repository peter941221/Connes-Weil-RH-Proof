# Proof 756: Direct Completed-Kernel Bridge

## Result

Proof 756 replaces the invalid source-basis-prefix route with a direct
completed signed-kernel owner for the physical target response.

Let

```text
B_(a,c) = sourceCompletedSignedKernelBoundaryOperator_(a,c)
R        = sourceSoninProjection
W        = detectorOperator
L_S      = sourcePhysicalCoframeLeakage_S
J        = sourceInclusion.
```

The existing completed operator is the actual source commutator

```text
B_(a,c) = [R, W].                                      (756.1)
```

The target boundary commutator has the opposite orientation, so Lean proves

```text
[W, R] = -B_(a,c).                                     (756.2)
```

Combining `(756.2)` with the physical coframe response yields the direct
operator identity

```text
Target_S = L_S^* [W, R] J
         = -L_S^* B_(a,c) J.                           (756.3)
```

Every target diagonal is therefore the existing complete physical scalar, and
the ordinary diagonal trace is the existing full-kernel trace series.

```text
Target_S
   |
   |  exact orientation change: [W, R] = -[R, W]
   v
-L_S^* B_(a,c) J
   |
   v
complete outer + reflected-second-support + prolate scalar
```

## Why This Is The Valid Route

Proofs 754 and 755 rule out deriving spatial compact-root locality from an
arbitrary source Hilbert-basis prefix or from CCM24's Gaussian/Hermite cyclic
basis.  Equation `(756.3)` contains neither a source `HilbertBasis` argument
nor a finite prefix/compression.  It therefore gives the correct direct owner
to which a future compact-root estimate can be applied.

The reflected-boundary and global-basis arguments used to construct
`B_(a,c)` are existing Hilbert--Schmidt factorization witnesses.  They are not
a source-Sonin basis prefix and do not assert spatial locality by themselves.

## Lean Declarations

The new source module proves:

```text
sourceBoundaryCommutator_eq_neg_completedKernelBoundaryOperator
finiteEulerTargetCommutatorResponse_eq_completedKernelLeakageResponse
inner_completedKernelLeakageResponse_eq_obliqueShearFullKernelScalar
ordinaryTraceAlong_completedKernelLeakageResponse_eq_fullKernelTrace
```

The source module is

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSGatePhysicalCompletedKernelBridge.lean
```

The import-facing audit is

```text
ConnesWeilRH/Dev/
  CCM24FiniteSGatePhysicalCompletedKernelBridgeAudit.lean
```

## Scope

This is an exact owner and readout bridge only.  It does not provide a common
relative-displacement kernel for the full signed scalar, an inserted-prefix
locality theorem, a family-uniform bound, the finite-S sign, Burnol's identity,
or `_root_.RiemannHypothesis`.

The active analytic target remains a direct estimate of the complete signed
outer/reflected-second-support/prolate trace after compact-root support acts
and before the first absolute value.

## Verification

The Windows truth files were copied to the Ubuntu-24.04 WSL2 ext4 verification
tree before building.

```text
+------------------------------------------------------+----------------+
| target                                               | result         |
+------------------------------------------------------+----------------+
| Proof 756 source module                              | PASS, 3390 jobs|
| import-facing axiom audit                            | PASS           |
| CCM25Concrete aggregate                              | PASS, 4022 jobs|
| full repository                                      | PASS, 4103 jobs|
+------------------------------------------------------+----------------+
```

All four audited public theorems use exactly

```text
[propext, Classical.choice, Quot.sound]
```
