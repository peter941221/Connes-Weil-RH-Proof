# Proof 764: Canonical Adjoint Completed-Kernel Energy

## Result

Proof 764 gives an exact Hilbert--Schmidt pair owner for the adjoint of the
canonical Gate target. It turns one possible Gate 3U route into a single,
explicit right-leg energy obligation. It does not prove that obligation.

Write

```text
B     = sourceCompletedSignedKernelBoundaryOperator,
J     = sourceInclusion,
L_S   = sourcePhysicalCoframeLeakage,
Target_S = -L_S^dagger B J.
```

The completed boundary is skew-adjoint. Taking the adjoint of `Target_S` and
using the existing physical pair gives a new pair with

```text
newPair.left  = base.left  o J,
newPair.right = base.right o L_S,
newPair.traceProduct = Target_S^dagger.                 (764.1)
```

No trace cycle, source-basis prefix, or physical-branch rearrangement is used
in `(764.1)`.

## Exact Energy Handoff

The fixed inclusion leg is already controlled:

```text
sum_i ||newPair.left(e_i)||^2
  <= fixedPhysicalEnergyMajorant.                       (764.2)
```

Define the complete right leakage energy by

```text
E_right(S)
 :=sum_i ||base.right(L_S e_i)||^2.                     (764.3)
```

Lean proves that this is definitionally the right energy of `newPair`. Hence
one additional source theorem

```text
E_right(S) <= fixedPhysicalEnergyMajorant               (764.4)
```

implies, by one Hilbert--Schmidt Cauchy--Schwarz inequality,

```text
abs(Re Tr(Target_S))
  <= fixedPhysicalEnergyMajorant.                       (764.5)
```

The canonical-family specialization feeds `(764.4)` directly into
`canonicalRealGate3UAt` from Proof 761.

```text
fixed completed left energy
             +
complete finite-S right leakage energy
             |
             v
one Cauchy--Schwarz operation
             |
             v
canonical real Gate bound
```

## Why This Does Not Close Gate 3U

Condition `(764.4)` is sufficient, but it is stronger than the signed scalar
estimate that Gate 3U actually asks for. The physical pair is an orthogonal
sum of the outer, reflected second-support, and prolate coordinates. Its
positive right energy has the schematic form

```text
||B_outer L_S||^2
  +||B_second L_S||^2
  +||B_prolate L_S||^2.                                (764.6)
```

The Gate scalar instead retains their signs and cross-orientation pairing:

```text
<A_outer,B_outer L_S>
  +<A_second,B_second L_S>
  -<A_prolate,B_prolate L_S>.                          (764.7)
```

Passing from `(764.7)` to `(764.6)` deletes the cancellation that compact-root
support acts on. Proof 260 gives the exact guard: a completed crossing can
have zero scalar trace outside the support window while every two-Hilbert--
Schmidt factor norm retains strictly positive nuclear mass. Therefore a
branch-packed square energy is a valid sufficient condition, but it must not
be presented as the shortest verified Gate 3U estimator.

The available contraction also does not repair this. Lean proves contractivity
only after multiplying `L_S` by both finite-Euler lower factors:

```text
(product_(p in S)(1-p^(-1/2)))^2 L_S.                  (764.8)
```

Dividing `(764.8)` loses the collapsing lower factor and does not yield a
support-polynomial bound for the raw canonical target.

## Lean Owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCanonicalAdjointEnergyGate.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCanonicalAdjointEnergyGateAudit.lean

ConnesWeilRH/Source/CCM25Concrete.lean
```

The public declarations are

```text
finiteEulerCompletedKernelAdjointTargetPairData
finiteEulerCompletedKernelAdjointTargetPairData_traceProduct_eq
sourcePhysicalCoframeCompletedKernelRightEnergy
finiteEulerCompletedKernelAdjointTargetPairData_right_energy_eq
finiteEulerCompletedKernelAdjointTargetPairData_left_energy_le
abs_re_ordinaryTraceAlong_targetCommutator_le_of_rightEnergy
canonicalRealGate3UAt_of_completedKernelRightEnergy
```

## Verification

The Windows source files were copied one way into the Ubuntu-24.04 WSL2 ext4
verification tree before the acceptance batch.

```text
+-------------------------------------------+-----------------+
| target                                    | result          |
+-------------------------------------------+-----------------+
| focused source                            | PASS            |
| import-facing audit                       | PASS, 3403 jobs |
| CCM25Concrete aggregate                   | PASS, 4028 jobs |
| full repository                           | PASS, 4109 jobs |
+-------------------------------------------+-----------------+
```

Every audited theorem uses exactly

```text
[propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, user axiom, heartbeat override, or recursion-depth
override was added.

## Status

```text
+--------------------------------------+----------+
| statement                            | status   |
+--------------------------------------+----------+
| adjoint completed-kernel pair        | PROVED   |
| fixed left-leg energy                | PROVED   |
| right leakage energy producer        | OPEN     |
| canonical completed signed estimate  | OPEN     |
| Gate 3U                              | OPEN     |
| finite-S sign                        | OPEN     |
| Burnol identity                      | OPEN     |
| Riemann Hypothesis                   | UNPROVED |
+--------------------------------------+----------+
```

The active route remains a direct estimate of the complete signed scalar,
for example Proof 413's relative-displacement functional or Proof 416's
completed Burnol boundary estimate, before the first absolute value.
