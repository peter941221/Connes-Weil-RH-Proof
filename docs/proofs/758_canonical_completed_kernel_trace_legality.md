# Proof 758: Canonical Completed-Kernel Trace Legality

## Result

Proof 758 gives the literal finite-S target commutator a genuine
Hilbert--Schmidt pair owner on the source Sonin carrier.  Consequently its
diagonal is summable along every named source Hilbert basis supplied to the
physical construction.

Let

```text
B_(a,c) = completed outer + reflected-second-support + prolate boundary pair,
L_S     = sourcePhysicalCoframeLeakage_S,
J       = sourceInclusion,
Target_S = finiteEulerTargetCommutatorResponse_S.
```

Proof 756 gives

```text
Target_S = -L_S^* B_(a,c) J.
```

Proof 758 defines one pair by precomposing both legs of `B_(a,c)` and placing
the sign in the shared right leg:

```text
TargetPair_S
  = boundedPrecomp(B_(a,c), L_S, J).smulRight(-1).
```

Lean proves its trace product is exactly the literal target:

```text
TargetPair_S.traceProduct = Target_S.
```

Therefore, for every named source basis `e_i`, the canonical scalar from
Proof 757 satisfies

```text
Summable (fun i => K_S(e_i)),
K_S(x) = <x, Target_S x>.
```

```text
completed three-branch physical pair
       |  outer + reflected + prolate stay coupled
       v
bounded precomposition by L_S and J; sign in one right leg
       |
       v
TargetPair_S.traceProduct = Target_S
       |
       v
Summable_i <e_i, Target_S e_i>
```

## What `IsTraceClassAlong` Means Here

The repository definition is intentionally narrow:

```text
IsTraceClassAlong(e, T)
  := Summable (fun i => <e_i, T e_i>).
```

It is named-basis diagonal legality.  It is not an assertion that the
operator is trace class in a basis-independent operator-ideal sense.

## Scope

The result is a fixed-family legality theorem.  It does not establish any of
the following:

```text
named-basis diagonal summability
  != basis-independent ordinary trace
  != uniform bound in the finite prime family
  != Gate 3U
  != finite-S sign, Burnol identity, or RH.
```

The physical support window and factorization witnesses remain explicit in
the pair construction.  Proof 757 still supplies the separate fact that the
resulting scalar is canonical across those witnesses.

## Lean Declarations

```text
finiteEulerCompletedKernelTargetPairData
finiteEulerCompletedKernelTargetPairData_traceProduct_eq
finiteEulerTargetCommutatorResponse_isTraceClassAlong_completedKernel
summable_finiteEulerCanonicalCompletedKernelDiagonal
```

Source:

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSGatePhysicalCanonicalCompletedKernelTraceLegality.lean
```

Audit:

```text
ConnesWeilRH/Dev/
  CCM24FiniteSGatePhysicalCanonicalCompletedKernelTraceLegalityAudit.lean
```

## Verification

Windows truth files were synchronized to an Ubuntu-24.04 WSL2 ext4
verification copy before the batch builds.

```text
+------------------------------------------------------+----------------+
| target                                               | result         |
+------------------------------------------------------+----------------+
| Proof 758 source module                              | PASS, 3392 jobs|
| import-facing three-declaration axiom audit          | PASS           |
| CCM25Concrete aggregate                              | PASS, 4024 jobs|
| full repository                                      | PASS, 4105 jobs|
+------------------------------------------------------+----------------+
```

Every audited theorem uses exactly

```text
[propext, Classical.choice, Quot.sound]
```

The new source and audit contain no `sorry`, `admit`, user axiom, unsafe
declaration, or heartbeat/recursion-limit override.
