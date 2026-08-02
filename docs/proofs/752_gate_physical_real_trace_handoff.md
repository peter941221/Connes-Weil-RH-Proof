# Proof 752: Gate Physical Real Trace Handoff

## Result

Proof 752 connects the real part of the existing lower-factor Gate trace to
the one complete physical full-kernel scalar.  It does not claim a complex
Gate 3U bound.

Let

```text
G_S = Tr(lowerFactorGaugedActualBandCompletedRelativeResponse_S),
J_S = Tr(sourceActualBandFiniteEulerSoninResponse_S),
K_S = finiteEulerObliqueShearFullKernelTrace_S.
```

Lean proves

```text
Re(G_S) = Re(J_S) + Re(K_S).                           (RH.1)
```

The first jet has the existing family-independent support majorant.  Hence

```text
abs(Re(G_S)) <= M + abs(Re(K_S)),
abs(Re(K_S)) <= abs(Re(G_S)) + M.                       (RH.2)
```

Consequently, uniform real boundedness of the Gate trace is equivalent to
uniform boundedness of `abs(Re(K_S))`; it is also equivalent to uniform
boundedness of Proof 751's normalized symmetric trace.

```text
+------------------------------+----------------------------------------+
| object                       | status                                 |
+------------------------------+----------------------------------------+
| first-jet real trace         | uniformly controlled by existing M     |
| full-kernel real trace       | exact remaining analytic scalar        |
| Gate real trace              | equivalent up to the first-jet term    |
| Gate complex-norm contract   | still stronger and still open          |
| Gate 3U / finite-S sign / RH | open                                   |
+------------------------------+----------------------------------------+
```

## Why The Split Is Legal

The first jet and physical leakage are separately trace legal for each fixed
family.  The proof only applies the real-part map after the complete physical
leakage scalar has been formed:

```text
lower-factor Gate trace
  = first jet + physical leakage
  = first jet + conjugate(target trace)
  = first jet + conjugate(full-kernel trace).
```

The outer compact-root, reflected second-support, and prolate terms remain
inside `K_S` before this real readout.  No triangle inequality splits them.

## Scope

This is a real-trace interface, not a proof that the full complex target trace
is real.  In particular, it does not allow the current complex-norm Gate 3U
consumer to be replaced without a downstream route audit.

The source module is

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSGatePhysicalRealTraceHandoff.lean
```

The audit module is

```text
ConnesWeilRH/Dev/
  CCM24FiniteSGatePhysicalRealTraceHandoffAudit.lean
```

## Verification

The accepted WSL2 ext4 verification batches were

```text
+------------------------+-----------+
| batch                  | result    |
+------------------------+-----------+
| focused source + audit | 3396/3396 |
| aggregate + audit      | 4021/4021 |
| full repository        | 4101/4101 |
+------------------------+-----------+
```

All six audited public theorems use exactly

```text
[propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, user axiom, unsafe declaration, heartbeat override,
recursion-limit override, long line, or trailing whitespace was added to the
source or audit.
