# Proof 723: Physical Cancellation Gate Bridge

Proof 722 made the remaining endpoint contraction equivalent to the
same-object cancellation

```text
sourceActualBandForwardCoframe
  + sourcePhysicalCoframeLeakage = 0.
```

Proof 723 feeds that exact equation into the existing Gate consumers. The new
source-facing declarations are

```text
sourceActualBandCombinedPhysicalRightEnergy_le_of_forward_add_physicalLeakage_eq_zero
lowerFactorGauged_trace_norm_le_of_forward_add_physicalLeakage_eq_zero
```

The first theorem rewrites the cancellation through Proof 721/722 into
`‖sourceActualBandForwardEndpointCoframe‖ <= 1`, then applies the existing
combined-energy contraction reduction. The second theorem passes that energy
bound into the uncomposed endpoint Gate bridge and obtains the already-known
family-independent trace bound

```text
‖ordinaryTraceAlong sourceBasis lowerFactorGaugedActualBandCompletedRelativeResponse‖
  <= 2 * fixedPhysicalEnergyMajorant.
```

This is still conditional. It does not prove the physical cancellation,
Gate 3U, the finite-S sign, Burnol's identity, or `_root_.RiemannHypothesis`.
Its purpose is to make the next producer target exact: prove the one coherent
operator equation before taking norms or traces.
