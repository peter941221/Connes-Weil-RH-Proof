# 1923 — Route A Round 2: current-selector API underdetermination

Date: 2026-09-24.

Status: scoped API no-go. This record does not claim that a strengthened
correction selector cannot close the signed budget, and RH is not claimed.

## Target

For the actual selected owner used by Route A, Round 2 asked for a strict
margin of the form

```text
archimedeanTerm(selectedOwner.square)
  + integral (-t * actualAggregateDerivative(t))
  <= -epsilon,  epsilon > 0.
```

The finite visible-prime sum had to stay grouped inside the actual aggregate
derivative. A primewise absolute-value majorant would remove the cancellation
that the route is trying to prove.

## Dependency audit

The selected correction is produced by
`ConnesWeilRH/Dev/C1HealthyYoshidaCorrectionFamily.lean`.
`ResidualCorrectionFamily` contains exactly the following mathematical
constraints on `value y`:

```text
support (value y) ⊆ Set.Ioo lower upper
laplaceAt (value y) z = y z
```

The selector is a classical choice from the finite-node interpolation theorem.
The file explicitly does not assert positivity, affine structure, a canonical
linear choice, or P2 sufficiency.

The physical-kernel route in
`ConnesWeilRH/Dev/C1P2OrbitPhysicalKernelCoboundary.lean` defines the actual
residual as

```text
orbitPhysicalKernelCoboundaryResidual geometry t
  = -t * orbitFinitePhysicalKernelIntegrandDerivative geometry t
```

The derivative is built from the physical bilateral profile and the derivatives
of its shifted factors. Thus the desired sign needs information about physical
derivatives, phases, variation, or a directly proved signed integral. None of
those quantities is constrained by the two fields of `ResidualCorrectionFamily`.

The existing structure
`OrbitPhysicalKernelCoboundaryCertificate` contains
`residual_budget` as a field. Supplying that structure would assume the exact
Round-2 conclusion rather than prove it, so it cannot close this round.

## Round result

Named stop condition:

```text
NO-GO-A2-CURRENT-API
```

The current correction-selector API is insufficient to derive the signed
residual budget. This is a formal/API dependency audit, not a mathematical
no-go for every possible selector. The next legitimate Route-A attempt must
first construct a selector whose output carries independently proved physical
kernel derivative control; merely adding another certificate field or wrapper
does not count.

This satisfies the campaign stop rule by producing a named, source-referenced
no-go instead of silently treating the missing inequality as an assumption.
