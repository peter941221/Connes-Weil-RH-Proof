# Proof 707: Compact-Root Fourier Almost-Everywhere Nonvanishing Bridge

## What is established

For a compact logarithmic root `g`, assume:

```text
Fourier g.test is analytic on R
g.test != 0
```

The isolated-zero theorem gives a codiscrete complement of the real zero set.
`ae_restrict_le_codiscreteWithin` then turns that topological statement into
Lebesgue almost-everywhere nonvanishing, and the result is transported to the
actual `Lp` representative used by the convolution multiplier.

The declaration is

```text
fourier_test_ae_ne_zero_of_analytic_of_test_ne_zero
```

This is a zero-set consumer.  It does not prove that the Fourier transform of
the current compact root is analytic, and it does not infer root nonzero-ness
from the selected owner without an explicit arithmetic producer.

## Position in the chain

```text
root nonzero + analytic Fourier producer
             |
             v
original-root Fourier != 0 a.e.
             |
             v
Proof 706 full-boundary injectivity adapter
```

The analytic Fourier producer, finite-window uniqueness, Gate 3U, the finite-S
sign, Burnol's identity, and `_root_.RiemannHypothesis` remain open.

## Verification

The focused source target passed in the Ubuntu-24.04 WSL2 ext4 mirror with
`3290/3290` jobs.  The import-facing audit passed and reported exactly
`[propext, Classical.choice, Quot.sound]`.  The `CCM25Concrete` aggregate
passed with `3980/3980` jobs, and the full repository build passed with
`4061/4061` jobs.  No `sorry`, `admit`, or user axiom was added.  The analytic
Fourier producer, finite-window uniqueness, Gate 3U, the finite-S sign,
Burnol's identity, and `_root_.RiemannHypothesis` remain open.
