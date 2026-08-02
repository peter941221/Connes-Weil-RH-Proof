# Proof 705: Reflected-Root Fourier Multiplier Bridge

## What is established

For a compact logarithmic root `g`, the involuted root used by the
full-boundary consumer satisfies the exact pointwise Fourier identity

```text
Fourier (g.involution.test) xi
  = conj (Fourier g.test xi).
```

Therefore an almost-everywhere nonvanishing Fourier multiplier for the
original root transfers to the involuted root.  The Lean declarations are

```text
fourier_involution_test_apply
fourier_involution_test_ae_ne_zero_of_fourier_test_ae_ne_zero
```

The proof uses only the Fourier integral, reflection change of variables, and
complex conjugation.  The source declaration reuses the already established
`SelectedCrossingOperatorBridge.fourier_compactLogTest_involution` implementation
for that pointwise calculation, so the orientation and `Circle` character
bookkeeping are not duplicated here.  It does not use compactness as a
substitute for an analytic zero-set theorem.

## Position in the cancellation chain

```text
original-root Fourier nonvanishing
              |
              v
involuted-root Fourier nonvanishing
              |
              v
Proof 704 global convolution injectivity
              |
              v
finite-window uniqueness on translated Sonin input
```

Proof 705 removes the orientation/conjugation bookkeeping from the remaining
multiplier premise.  It does not prove original-root Fourier nonvanishing,
finite-window uniqueness, Gate 3U, the finite-S sign, Burnol's identity, or
`_root_.RiemannHypothesis`.  In particular, `HasCompactSupport` and ordinary
Fourier injectivity alone do not imply almost-everywhere nonvanishing of a
Fourier transform.

## Verification

The focused source target passed in the Ubuntu-24.04 WSL2 ext4 mirror with
`3288/3288` jobs.  The import-facing audit also passed after the source object
was built.  The `CCM25Concrete` aggregate passed with `3978/3978` jobs, and
the full repository build passed with `4059/4059` jobs.

Both audited declarations use only

```text
[propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, or user axiom was added.  Gate 3U, finite-window
uniqueness, original-root Fourier nonvanishing, the finite-S sign, Burnol's
identity, and `_root_.RiemannHypothesis` remain open.
