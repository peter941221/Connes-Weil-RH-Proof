# Proof 700: Fixed Physical Kernel Bridge

## What is established

The fixed physical source input is the positive Gram square root of the
complete three-branch physical pair.  Its dense-range problem can be reduced
without an estimate to the two actual translated compact boundary legs of the
outer physical branch.

For the product-valued right leg, Lean proves

```text
l2Sum.right x = 0
  <-> first.right x = 0 and second.right x = 0.
```

The complete fixed-source implication is

```text
fixed physical right leg = 0
  -> complete three-branch right leg = 0
  -> outer signed pair right leg = 0
  -> translated negative and positive boundary legs = 0.
```

The final theorem is
`fixedPhysicalSourceInput_denseRange_of_translated_boundary_pair_injective`.
It constructs

```text
DenseRange fixedPhysicalSourceInput
```

under the explicit source condition

```text
forall x,
  translated.left (sourceInclusion x) = 0
  -> translated.right (sourceInclusion x) = 0
  -> x = 0.
```

## Why the condition remains explicit

The bridge does not infer Fourier-multiplier injectivity.  Energy summability,
positivity, Hilbert--Schmidt compactness, and a Gram square root do not imply
that the two actual translated boundary legs have no common null vector.  The
joint injectivity statement is therefore still an analytic source obligation.

This is the legal condition needed by Proof 698 to remove the common source
input from the completed-history endpoint readout.  It does not prove Gate 3U,
the finite-S sign, Burnol's identity, or unconditional
`_root_.RiemannHypothesis`.

## Verification

The WSL2 focused build was:

```text
lake build ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedPhysicalKernelBridge \
  ConnesWeilRH.Dev.CCM24FiniteSFixedPhysicalKernelBridgeAudit
```

The focused source and audit completed with `3285` jobs.  The aggregate
`ConnesWeilRH.Source.CCM25Concrete` completed with `3973` jobs, and the full
default build completed with `4054` jobs.  The audited declarations use exactly

```text
[propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, or user axiom was added.
