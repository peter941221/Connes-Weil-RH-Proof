# 079 - Finite physical-kernel node certificate route socket

Date: 2026-09-21.

Status: formal consumer interface landed; the signed certificate remains open.
This record is subordinate to the binding B5 route in [003](003_b1_b5_minimal_exit_route_selection.md).

## Result

The actual selected `OrbitG8Geometry` owner has a finite visible-prime range.
For a function `nodeBound : Nat -> Real`, Lean now accepts the following
certificate shape:

```text
archimedeanTerm(g * g) + sum_{n in visible range} nodeBound(n) <= 0
every actual physical-kernel prime term(n) <= nodeBound(n)
```

The first theorem produces `orbitWindowSemiLocalGate g`. The end-to-end
theorem `sourceRH_of_right_orbitGeometry_physicalKernel_nodeBounds`
quantifies this certificate over every right-hand off-line zero and produces
`RHDefinitionBridge.standard.SourceRH`.

## Evidence and boundary

Formal evidence:

- `ConnesWeilRH/Dev/C1P2OrbitPhysicalProfileReadback.lean`
- `orbitWindowSemiLocalGate_of_physicalKernel_nodeBounds`
- `sourceRH_of_right_orbitGeometry_physicalKernel_nodeBounds`
- paired audit module with standard axioms only

The focused audit build completed successfully with zero `error:` lines and
zero `sorryAx`. This record changes the producer target from an opaque finite
budget to a finite auditable certificate, but proves no node bound, no gate
sign, and no RH. Existing support, zero, and tail fields are representation
and health data; they do not imply signed prime estimates.

## Next mathematical target

For the actual constructor-selected correction, construct signed bounds for
the finite physical-kernel terms while retaining the Archimedean remainder.
Any proposed bound must be same-owner, finite-range, and compatible with the
correction's zero/tail data. Mellin interpolation alone is excluded by
[078](078_mellin_physical_separation.md), and pointwise profile negativity is
excluded by the earlier sign audit.
