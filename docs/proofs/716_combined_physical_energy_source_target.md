# Proof 716: Combined Physical Energy Source Target

The direct Gate consumer from Proof 715 is now connected to the exact
coframe ledger. The remaining source theorem must bound the complete response
before any branchwise absolute value:

```text
sourceActualBandForwardEndpointCoframe
  = sourceInclusion + sourceActualBandCombinedCoframeLeakage

sourceActualBandCombinedCoframeLeakage
  = sourceActualBandForwardCoframe
    + sourceSoninCoframeLeakage
```

The metric-history readout controls only the metric coframe. Existing guard
`metricHistoryReadout_eq_forwardEndpoint_iff_forward_zero` proves that it can
equal the full physical endpoint only if the actual forward coframe vanishes.
That vanishing is not available and must not be assumed.

Therefore the unique source target is:

```text
sum_i || rightLeg
  (sourceActualBandForwardEndpointCoframe (sourceBasis i)) ||^2
  <= fixedPhysicalEnergyMajorant
```

with the forward, outer, reflected, second-support, and prolate channels kept
as one coherent signed object. A triangle inequality over those channels is
not an acceptable Gate 3U producer.

Proof 715 already consumes this exact target and returns the signed trace
bound. Gate 3U, finite-S sign, Burnol's identity, and RH remain open.
