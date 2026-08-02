# Proof 759: Physical Completed-Kernel Trace Legality

## Result

Proof 759 carries Proof 758's fixed-family named-basis diagonal legality to
both concrete physical forms of the completed target:

```text
Target_S
  = CompletedLeakageResponse_S,

K_S(x)
  = sourceObliqueShearPhysicalFullKernelScalar_S(x).
```

For every named source Hilbert basis `e_i`, Lean now proves

```text
IsTraceClassAlong(e, CompletedLeakageResponse_S),
Summable (fun i => sourceObliqueShearPhysicalFullKernelScalar_S(e_i)).
```

Here `IsTraceClassAlong` has the project-local meaning of summability of the
named diagonal.  It is not a claim about a basis-independent trace ideal.

```text
Proof 758 physical pair
          |
          v
Target_S has a summable named diagonal
          |
          | Target_S = CompletedLeakageResponse_S
          v
direct completed response is trace-legal
          |
          | K_S(e_i) = full physical-kernel scalar(e_i)
          v
complete physical scalar series is summable
```

## Why This Matters

The direct completed response and the full physical-kernel series are the
forms used by later fixed-family trace manipulations.  This proof makes their
diagonal legality explicit from the same completed outer, reflected
second-support, and prolate pair.  It does not obtain legality by splitting
those branches or by invoking a trace cycle.

## Scope

```text
fixed-family named-basis summability
  != basis-independent ordinary trace
  != an interchange of finite-family and basis limits
  != a branchwise absolute-value estimate
  != a uniform Gate 3U bound.
```

The active analytic bottom is unchanged: compact-root support must act on the
one complete signed scalar before the first absolute value, followed by a
bound independent of the visible finite prime family.

## Lean Declarations

```text
finiteEulerCompletedKernelLeakageResponse_isTraceClassAlong
summable_sourceObliqueShearPhysicalFullKernelScalar
```

Source:

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSGatePhysicalCanonicalCompletedKernelPhysicalTraceLegality.lean
```

Audit:

```text
ConnesWeilRH/Dev/
  CCM24FiniteSGatePhysicalCanonicalCompletedKernelPhysicalTraceLegalityAudit.lean
```

## Verification

Windows truth files were synchronized to an Ubuntu-24.04 WSL2 ext4
verification copy before the batch builds.

```text
+------------------------------------------------------+----------------+
| target                                               | result         |
+------------------------------------------------------+----------------+
| Proof 759 source module                              | PASS, 3393 jobs|
| import-facing two-declaration axiom audit            | PASS           |
| CCM25Concrete aggregate                              | PASS, 4025 jobs|
| full repository                                      | PASS, 4106 jobs|
+------------------------------------------------------+----------------+
```

Both audited theorems use exactly

```text
[propext, Classical.choice, Quot.sound]
```

The new source and audit contain no `sorry`, `admit`, user axiom, unsafe
declaration, or heartbeat/recursion-limit override.
