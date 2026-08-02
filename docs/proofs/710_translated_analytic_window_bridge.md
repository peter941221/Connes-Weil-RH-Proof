# Proof 710: Translated Analytic-Window Bridge

## What is established

Proof 710 connects the Proof 709 analytic uniqueness consumer to the actual
translated `sourceSoninCarrier` premise used by the full-boundary chain.

The new finite-window contract is

```text
forall y : sourceSoninCarrier lambda,
  exists analytic representative f_y of
    cc20GlobalLogConvolution owner.sourceTest.involution.test
      (U_(log lambda) (sourceInclusion y))
```

With a nontrivial source window `a < c`, this contract proves the exact
translated window uniqueness premise consumed by Proof 704/706:

```text
globalL2ToKernelInterval (-c) (-a) 0 (translated convolution) = 0
  -> translated convolution = 0.
```

The module also composes this with the original-root multiplier chain:

```text
original-root Fourier != 0 a.e.
  + translated analytic-window representatives
  -> translated full-boundary injectivity.
```

Finally, it exposes two owner-level entry points: a nonzero finite-prime atom
or a selected visible prime, plus Fourier analyticity of the original root,
plus translated analytic-window representatives, imply translated
full-boundary injectivity.

## Declarations

```text
translated_window_unique_of_analytic_representatives
fullBoundaryRootFactor_injective_of_translated_analytic_window_of_original_fourierMultiplier
fullBoundaryRootFactor_injective_of_translated_analytic_window_of_finitePrimeTerm
fullBoundaryRootFactor_injective_of_translated_analytic_window_of_selectedVisiblePrime
```

## Boundary

This is still a bridge, not a Gate 3U producer.  It does not construct the
per-vector analytic representatives, prove Fourier analyticity of the current
root, prove the finite-S sign, prove Burnol's identity, or prove
`_root_.RiemannHypothesis`.

The point is narrower: the formerly naked finite-window uniqueness premise is
now a concrete analytic-representative source obligation on the exact
translated convolution vectors used by the route.

## Verification

Verification was run in the Ubuntu-24.04 WSL2 ext4 mirror under the shared
Lake lock:

```text
source target:
  flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build \
    ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedTranslatedAnalyticWindowBridge
  PASS: 3295/3295 jobs

audit target:
  flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build \
    ConnesWeilRH.Dev.CCM24FiniteSFixedTranslatedAnalyticWindowBridgeAudit
  PASS: 3296/3296 jobs

aggregate:
  flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build \
    ConnesWeilRH.Source.CCM25Concrete
  PASS: 3983/3983 jobs

full repository:
  flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build
  PASS: 4064 jobs
```

The import-facing audit prints exactly
`[propext, Classical.choice, Quot.sound]` for all four declarations.  No
`sorry`, `admit`, or user axiom was added.
