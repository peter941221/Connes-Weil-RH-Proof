# Proof 598: old-carrier coframe response bounds

## Result

The low-level module
`CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeResponseBounds.lean`
isolates the elementary contraction estimates needed by the old-carrier
coframe ledger. It installs the `CompleteSpace` instance on the actual source
Sonin subtype and proves, with the explicit `sourceInclusion` carrier:

```text
||forwardCoframe_S|| <= 1
||detectorOperator * sourceInclusion|| <= ||detectorOperator||
||forwardCoframe_S^dagger * detectorLeg|| <= ||detectorOperator||
||sourceInclusion^dagger * detectorOperator * forwardCoframe_S||
  <= ||detectorOperator||
```

The signed orientation row and survivor residual row are deliberately absent.
These estimates are bounded-leg bookkeeping; they do not produce the missing
source-specific two-channel Douglas readout.

## Verification

The import-facing audit is
`CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeResponseBoundsAudit.lean`.
The Ubuntu-24.04 WSL2 focused build used:

```text
flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build \
  ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeResponseBounds
```

The source build passed with `3347 jobs`. The audit build passed with `3348
jobs`, and all four audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The larger owner target still enters the known high-memory elaboration path;
that is a build-boundary issue, not evidence for an orientation or residual
estimate. Bone 1 remains open at the family-uniform signed source producer.
