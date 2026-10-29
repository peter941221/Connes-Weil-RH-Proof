# 3172: Route-A owner physical-kernel certificate contract

Status: Lean-verified on 2026-10-29 with the project Lean 4.30.0 toolchain.

This record moves the live producer obligation to the exact same-owner
physical-kernel interface. A node is represented as:

```text
signed center + nonnegative error
```

The contract requires two facts for the same `OrbitG8Geometry`:

1. each actual signed node lies within its center/error enclosure;
2. the sum of center plus error, together with the same owner's
   archimedean term, is nonpositive.

The module proves that this envelope produces an
`OrbitPhysicalKernelNodeCertificate`, then feeds the existing
`orbitWindowSemiLocalGate` consumer. It supplies no numerical centers,
errors, owner, or margin. It does not prove SourceRH or RH.

The audit file reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```
