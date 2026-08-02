# Proof 757: Canonical Completed-Kernel Readout

## Result

Proof 757 gives the completed physical response one canonical scalar target.
It removes dependence on the support-window and Hilbert--Schmidt
factorization witnesses from the scalar being estimated, while retaining the
named source basis where an ordinary diagonal series is required.

For a source vector `x`, define

```text
K_S(x) = <x, Target_S x>.
```

Here `Target_S` is the direct completed commutator response of Proof 756.
For every admissible support window and factorization witness, Lean proves

```text
K_S(x)
  = <x, CompletedLeakageResponse_(a,c) x>
  = sourceObliqueShearPhysicalFullKernelScalar_(a,c)(x).
```

The corresponding source-basis diagonal series is likewise canonical in
those physical witnesses:

```text
ordinaryTraceAlong(sourceBasis, Target_S)
  = sum_i K_S(sourceBasis_i)
  = FullKernelTrace_(a,c, sourceBasis).
```

```text
support window + factorization witnesses
                 |
                 v
completed physical response diagonal
                 |
                 | exact readback
                 v
K_S(x) = canonical completed-kernel scalar
                 |
                 v
named source-basis diagonal series
```

## Why This Matters

The active Gate 3U route must estimate one signed completed scalar after
compact-root support acts, with the outer, reflected second-support, and
prolate branches still coupled.  Proof 757 makes that scalar independent of
the auxiliary window and factorization data used to display its physical
formula.  A later bound can therefore target `K_S` directly rather than
compare different witness-specific formulas first.

## Guard

This is witness canonicalization, not trace canonicalization:

```text
canonical in support/factorization witnesses
  != basis-independent ordinary trace
  != family-uniform Gate 3U estimate.
```

`finiteEulerCanonicalCompletedKernelDiagonalSeries` still takes a named
source Hilbert basis.  The proof does not establish basis independence,
absolute summability, a compact-root estimate, the finite-S sign, Burnol's
identity, or `_root_.RiemannHypothesis`.

## Lean Declarations

The new source module proves:

```text
finiteEulerCanonicalCompletedKernelScalar
finiteEulerCanonicalCompletedKernelScalar_eq_directLeakageDiagonal
finiteEulerCanonicalCompletedKernelScalar_eq_obliqueShearFullKernelScalar
finiteEulerCanonicalCompletedKernelDiagonalSeries
ordinaryTraceAlong_targetCommutator_eq_canonicalCompletedKernelDiagonalSeries
finiteEulerCanonicalCompletedKernelDiagonalSeries_eq_obliqueShearFullKernelTrace
ordinaryTraceAlong_completedKernelLeakageResponse_eq_canonicalCompletedKernelDiagonalSeries
```

The source module is

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSGatePhysicalCanonicalCompletedKernel.lean
```

The import-facing audit is

```text
ConnesWeilRH/Dev/
  CCM24FiniteSGatePhysicalCanonicalCompletedKernelAudit.lean
```

## Verification

Windows truth files were synchronized to an Ubuntu-24.04 WSL2 ext4
verification copy before building.

```text
+------------------------------------------------------+----------------+
| target                                               | result         |
+------------------------------------------------------+----------------+
| Proof 757 source module                              | PASS, 3391 jobs|
| import-facing five-declaration axiom audit           | PASS           |
| CCM25Concrete aggregate                              | PASS, 4023 jobs|
| full repository                                      | PASS, 4104 jobs|
+------------------------------------------------------+----------------+
```

Every audited theorem uses exactly

```text
[propext, Classical.choice, Quot.sound]
```

The new source and audit also contain no `sorry`, `admit`, user axiom,
unsafe declaration, or heartbeat/recursion-limit override.
