# Proof 765: Canonical Completed-Kernel Boundary Cycle

## Result

Proof 765 cycles the canonical completed-kernel target from the source Sonin
carrier to the literal common completed-boundary carrier.  It uses the two
Hilbert--Schmidt legs already constructed in Proof 758 and keeps the outer,
reflected second-support, and prolate branches inside one operator.

Write

```text
B     = sourceThreeBranchPairData,
J     = sourceInclusion,
L_S   = sourcePhysicalCoframeLeakage,

A_S   = B.left o L_S,
C     = -(B.right o J).
```

The source target is the rectangular product

```text
Target_S = A_S^dagger C,
```

and the completed-boundary cycle is the opposite product

```text
BoundaryCycle_S = C A_S^dagger
                =-(B.right o J o L_S^dagger o B.left^dagger).   (765.1)
```

The pair coefficient matrix is absolutely summable over the source and
boundary Hilbert bases.  Therefore Lean proves the genuine rectangular trace
cycle

```text
Tr_source(Target_S)=Tr_boundary(BoundaryCycle_S).                (765.2)
```

This is not an appeal to a finite-dimensional matrix identity.  Both products
are owned by explicit Hilbert--Schmidt pairs on their respective carriers.

```text
source Sonin carrier                 common boundary carrier
       |                                      |
       | A_S                                  | C
       v                                      v
common boundary carrier <---------------- source Sonin carrier

        A_S^dagger C          <----cycle---->       C A_S^dagger
             |                                        |
             +---------------- same trace ------------+
```

## Basis Independence

Equation `(765.2)` has two concrete consequences.

```text
ordinaryTraceAlong(sourceBasis, Target_S)
```

is independent of the supplied source Hilbert basis, and

```text
ordinaryTraceAlong(boundaryBasis, BoundaryCycle_S)
```

is independent of the supplied common-boundary Hilbert basis.  The boundary
operator also has a summable diagonal along every supplied boundary basis.

For the canonical support-coupled family, the corrected real Gate contract
from Proof 761 is exactly

```text
abs(Re Tr_boundary(BoundaryCycle_S)) <= bound.                    (765.3)
```

Thus `(765.3)` is a basis-free location for the same Gate 3U scalar.  It is
not the missing family-uniform estimate.

## Renewal-Fubini Guard

The pair theorem proves absolute summability only for the two Hilbert-basis
indices used in the rectangular trace cycle.  It does not prove absolute
summability after introducing a third renewal or Euler-update index.

In particular, Proof 765 does not authorize

```text
sum_sourceBasis (sum_renewal coefficient)
  = sum_renewal (trace renewalAtom).                              (765.4)
```

To use `(765.4)`, a later theorem must supply a common absolutely summable
majorant for the joint basis/renewal family, or prove convergence of the
complete signed renewal before taking the trace.  Fixed-family trace legality
alone is insufficient.

This distinction matters because Proof 260 shows that termwise
Hilbert--Schmidt or nuclear norms retain positive boundary mass even when the
completed compact-root scalar cancels exactly.  The valid Gate route must
still apply compact-root support to the complete signed boundary scalar before
the first absolute value.

## Lean Declarations

```text
finiteEulerCompletedKernelTargetBoundaryCycle
finiteEulerCompletedKernelTargetPairData_cyclic_eq
finiteEulerCompletedKernelBoundaryCyclePairData
finiteEulerCompletedKernelBoundaryCyclePairData_traceProduct_eq
ordinaryTraceAlong_targetCommutator_eq_completedBoundaryCycle
finiteEulerCompletedKernelTargetBoundaryCycle_isTraceClassAlong
ordinaryTraceAlong_targetCommutator_sourceBasis_independent
ordinaryTraceAlong_completedBoundaryCycle_basis_independent
canonicalRealGate3UAt_iff_completedBoundaryCycleRealBound
```

Source:

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCanonicalCompletedKernelBoundaryCycle.lean
```

Audit:

```text
ConnesWeilRH/Dev/
  CCM24FiniteSCanonicalCompletedKernelBoundaryCycleAudit.lean
```

## Verification

The Windows source files were copied one way into the Ubuntu-24.04 WSL2 ext4
verification tree before the acceptance build.

```text
+------------------------------------------------------+----------------+
| target                                               | result         |
+------------------------------------------------------+----------------+
| import-facing seven-theorem axiom audit              | PASS, 3404 jobs|
+------------------------------------------------------+----------------+
```

All seven audited theorems use exactly

```text
[propext, Classical.choice, Quot.sound]
```

## Status

```text
+--------------------------------------+----------+
| statement                            | status   |
+--------------------------------------+----------+
| rectangular completed-boundary cycle | PROVED   |
| source-basis independence            | PROVED   |
| boundary-basis independence          | PROVED   |
| renewal-index Fubini theorem         | OPEN     |
| family-uniform signed estimate       | OPEN     |
| Gate 3U                              | OPEN     |
| finite-S sign                        | OPEN     |
| Burnol identity                      | OPEN     |
| Riemann Hypothesis                   | UNPROVED |
+--------------------------------------+----------+
```

Proof 766 shows that a direct identification with Proof 262 would omit the
moving outer-projection endpoint.  The corrected bridge is a three-term trace
ledger: completed boundary equals outer anomaly minus transported-band
response.  The outer channel is the ambient Markov term; the transported-band
channel retains Proof 262's shorted Sonin defect.
