# Proof 724: Physical Cancellation Channel Split

Proof 723 made the Gate-facing hypothesis exact:

```text
sourceActualBandForwardCoframe
  + sourcePhysicalCoframeLeakage = 0.
```

Proof 724 rewrites the physical leakage into two same-carrier channels:

```text
sourcePhysicalCoframeLeakage
  = sourceOuterCoframeLeakage
    + sourceBandMetricCoframeLeakage
```

where

```text
sourceBandMetricCoframeLeakage
  = sourceBandProjection o finiteEulerMetricCoframe.
```

The new source-facing declarations are

```text
sourceSecondSupport_add_prolateCoframeLeakage_eq_bandMetricCoframeLeakage
sourcePhysicalCoframeLeakage_eq_outer_add_bandMetric
sourceActualBandForward_add_physicalLeakage_eq_outer_add_forward_add_bandMetric
norm_sourceActualBandForwardEndpointCoframe_le_one_iff_outer_add_forward_add_bandMetric_eq_zero
```

The core algebra is the pointwise projection ledger

```text
E(E D - Q E D) + (E Q E D - R D)
  = E D - R D,
```

using only idempotence of the radial projection on its own range.  In words:
the second-support branch plus the prolate correction recombine to the source
radial-Sonin band projection of the metric coframe.

The resulting endpoint-contraction target is therefore

```text
sourceOuterCoframeLeakage
  + (sourceActualBandForwardCoframe + sourceBandMetricCoframeLeakage)
  = 0.
```

This is an algebraic channel split only.  It does not prove either channel
vanishes separately, does not justify branchwise estimates, and does not prove
Gate 3U, the finite-S sign, Burnol's identity, or
`_root_.RiemannHypothesis`.  The next producer must keep the outer channel
and the forward-plus-band channel as one coherent signed equation unless a
new theorem proves an exact orthogonality or cancellation law.
