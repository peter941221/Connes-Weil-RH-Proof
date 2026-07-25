# Proof 528: graph physical boundary-target readback

## Result

Proof 527 expresses the actual endpoint as a graph endpoint plus one signed
endpoint residual.  Proof 528 pushes that identity through the existing
`physicalBoundaryDaggerTarget` used by the completed physical-history readout:

```text
physicalBoundaryDaggerTarget(rightLeg, actualEndpoint, inclusion, survivor)
  = graphBoundaryTarget(rightLeg, graphEndpoint, inclusion, survivor)
    + rightLeg * graphEndpointResidual.
```

The residual is now on the exact output carrier consumed by the future
physical boundary readout producer.  The second theorem is a definitional
readback of the right-leg composition, so no hidden carrier or operator order
is introduced.

The module also performs the required signed cancellation before estimation:

```text
endpointResidual
  = sourceBandProjection
      * (normalizedFiniteEulerInverse - fullGraphPhysicalProduct)
      * sourceInclusion.
```

The actual Schur product cancels exactly.  This direct owner must remain one
subtraction; separately bounding the physical-inverse and graph-cascade terms
would discard the cancellation needed by the Gate 3U route.

This is an exact same-object target assembly.  It does not prove that the
residual factors through the Julia co-defect, provide a family-uniform bound,
close Gate 3U, prove the finite-S sign, supply Burnol's identity, or prove RH.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSActualSchurGraphPhysicalBoundaryTargetReadback.lean
ConnesWeilRH/Dev/
  CCM24FiniteSActualSchurGraphPhysicalBoundaryTargetReadbackAudit.lean
```

The focused audit is expected to use only
`[propext, Classical.choice, Quot.sound]`.
