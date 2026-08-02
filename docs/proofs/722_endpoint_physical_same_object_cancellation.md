# Proof 722: Endpoint Physical Same-Object Cancellation

The endpoint iff from Proof 721 can now be read in the actual physical
decomposition.  The existing source identity

```text
sourceSoninCoframeLeakage = sourcePhysicalCoframeLeakage
```

is composed with the complete endpoint leakage identity to give

```text
sourceActualBandCombinedCoframeLeakage
  = sourceActualBandForwardCoframe
    + sourcePhysicalCoframeLeakage.
```

Therefore the exact Proof 717 contraction target is

```text
‖endpoint‖ <= 1
  <-> sourceActualBandForwardCoframe
      + sourcePhysicalCoframeLeakage = 0.
```

The Lean declarations are

```text
sourceActualBandCombinedCoframeLeakage_eq_forward_add_physicalLeakage
norm_sourceActualBandForwardEndpointCoframe_le_one_iff_forward_add_physicalLeakage_eq_zero
```

This is a same-object cancellation equation.  The physical leakage remains
the complete outer, second-support, and prolate sum; the raw forward coframe
is not discarded.  No branchwise triangle inequality, absolute-value bound,
trace cycle, or sign claim is used.  In particular, the existing physical
response identity does not prove this cancellation.

Gate 3U, the finite-S sign, Burnol's identity, and `_root_.RiemannHypothesis`
remain open.
