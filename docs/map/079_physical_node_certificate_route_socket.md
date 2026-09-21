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

The new module `C1P2OrbitPhysicalKernelIntegrandBounds` supplies the next
formal bridge: an almost-everywhere real majorant for the weighted physical
kernel integrand yields an integral upper bound, and paired majorants at
`+log n` and `-log n` yield the signed finite node bound after multiplication
by the nonnegative von Mangoldt coefficient. This is formal infrastructure,
not the analytic certificate itself. The same module now proves that the
weighted kernel integrand is integrable for every selected geometry by reducing
it to an exponential-weighted compact convolution. Thus the remaining
producer obligation is only to construct explicit same-owner integrable
majorants for the selected orbit correction and to bound the Archimedean
remainder.

The same module now packages the remaining analytic input as the
data-bearing `OrbitPhysicalKernelIntegrandCertificate`: per visible node it
stores plus/minus integrable majorants, almost-everywhere signed inequalities,
and one finite Archimedean budget. Its constructor produces the existing
`OrbitPhysicalKernelNodeCertificate` without changing owners. This is the
current fastest producer socket; the stored inequalities and budget are still
open mathematics, not assumptions discharged by the route.
