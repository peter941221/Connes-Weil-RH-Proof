# 081 — Same-owner physical-kernel coboundary certificate

Date: 2026-09-22.

Status: formal reduction brick complete; the certificate's analytic fields
remain open. This record is subordinate to the binding B5 route in [003](003_b1_b5_minimal_exit_route_selection.md).

Consumer: the healthy `CompactLog`, detector-specific B5 statement
`0 <= qw g`, through the existing `orbitWindowSemiLocalGate` and
`SourceRH` consumers.

## Result

`C1P2OrbitPhysicalKernelCoboundary` adds the owner-preserving structure
`OrbitPhysicalKernelCoboundaryCertificate`. Its derivative identity is typed
against the actual aggregate
`orbitFinitePhysicalKernelIntegrand`, so visible-prime cancellation remains
inside one summed physical profile. It records:

```text
F(t) = Q'(t) + residual(t)
Q(left) = Q(right) = 0
ArchimedeanTerm(g.square) + integral residual <= 0
```

The formal theorem
`intervalIntegral_orbitFinitePhysicalKernelIntegrand_eq_residual` proves the
exact interval readback. The gate consumer and the end-to-end
`sourceRH_of_right_orbitGeometry_coboundaryCertificate` are also wired.

The same leaf now proves continuity of the one-channel weighted kernel and of
the finite aggregate. This is the regularity input needed for a constructive
primitive `Q`; it still does not identify the primitive or prove a residual
sign.

It now also proves `DifferentiableAt` for both the one-channel weighted kernel
and the finite aggregate. The proof explicitly transports derivatives through
the real-to-complex cast, reflection, conjugation, and finite visible-prime
sum. This closes the formal regularity prerequisite for an actual derivative
expansion; it remains no sign estimate.

The leaf now additionally provides an explicit `HasDerivAt` formula for the
one-channel kernel and its finite visible-prime aggregate. A concrete primitive
is supplied:

```text
Q(t) = t * F(t)
residual(t) = -t * F'(t)
```

where `F` is the actual finite signed aggregate. The derivative identity
`F = Q' + residual` is formal, and both endpoint equalities follow from the
strict raw-factor support window. All prime cancellation remains inside the
single aggregate derivative. The residual budget itself is still open.

## Boundary

This is not yet the analytic producer. The concrete `Q`, residual, derivative
identity, and endpoint equalities are now supplied; the remaining obligation is
the same-owner residual budget
`archimedeanTerm + integral (-t * F'(t)) <= 0` for the selected orbit detector.
The raw-square tail is not used as a substitute for physical support. No
primewise absolute-value estimate, Mellin-only interpolation, parity
substitution, or RH conclusion is introduced.

Evidence: `ConnesWeilRH/Dev/C1P2OrbitPhysicalKernelCoboundary.lean` and its
paired Audit module. Classification: formal project-candidate interface;
analytic existence/sign remains an open mathematical obligation.
