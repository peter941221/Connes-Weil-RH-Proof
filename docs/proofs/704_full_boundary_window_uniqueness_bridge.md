# Proof 704: Full-Boundary Window-Uniqueness Bridge

## What is established

The full boundary factor is the reflected finite-window readout of a genuine
global convolution.  Proof 704 separates the remaining injectivity chain into
two source obligations:

```text
finite-window readout = 0
        |
        v
global root convolution = 0       [window uniqueness]
        |
        v
Fourier multiplier * Fourier(input) = 0
        |
        v
Fourier multiplier != 0 a.e.       [root frequency nondegeneracy]
        |
        v
translated source input = 0
```

The theorem
`cc20GlobalLogConvolution_injective_of_fourierMultiplier_ae_ne_zero` proves
the second half of this chain on the actual `Lp` carrier.  It uses
`fourier_globalLogConvolution`, the pointwise `Lp` product formula, and
injectivity of the Plancherel Fourier isometry.  The theorem
`fullBoundaryRootFactor_injective_of_translated_window_unique` then consumes
an explicit finite-window uniqueness premise and returns

```text
fullBoundaryRootFactor owner.sourceTest a c
    (U_(log lambda) (sourceInclusion lambda y)) = 0
  -> y = 0.
```

The final source-carrier step uses the genuine translation isometry and the
literal subtype inclusion; it does not use an oblique projection or an
unproved Fourier multiplier claim.

## Remaining obligation

The new `hwindow` premise is the exact unresolved analytic producer:

```text
restricted root convolution = 0
  -> global root convolution = 0
```

on the translated `sourceSoninCarrier`.  Proof 704 does not infer this from
compactness, support, positivity, or a nonzero root.  A nonzero compact root
only gives the global convolution conclusion after its Fourier multiplier is
proved nonzero almost everywhere; it does not by itself make a finite-window
readout injective.

Therefore Gate 3U, the finite-S sign, Burnol's identity, and
`_root_.RiemannHypothesis` remain open.

## Verification

The focused source and audit passed in Ubuntu-24.04 WSL2 with `3288` jobs.
Both audited declarations use exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, or user axiom was added.  The aggregate and full builds
must still be run after the aggregate import is synchronized.
