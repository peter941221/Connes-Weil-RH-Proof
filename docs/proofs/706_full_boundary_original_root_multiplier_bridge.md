# Proof 706: Full-Boundary Original-Root Multiplier Bridge

## What is established

The existing full-boundary injectivity consumer expects the Fourier multiplier
of `owner.sourceTest.involution.test` to be nonzero almost everywhere.  Proof
705 proves that this follows from the corresponding premise for the original
root.  Proof 706 wires the two declarations together:

```text
original-root Fourier nonvanishing
              |
              v
involuted-root Fourier nonvanishing
              |
              v
full-boundary injectivity under finite-window uniqueness
```

The declaration is

```text
fullBoundaryRootFactor_injective_of_translated_window_unique_of_original_fourierMultiplier
```

It consumes the same explicit finite-window premise as Proof 704.  The result
is a clean caller-facing contract; it does not infer either premise from
support, compactness, positivity, or root nondegeneracy.

## Remaining obligation

The actual source producer must still establish original-root Fourier
nonvanishing almost everywhere and the finite-window uniqueness implication
on the translated `sourceSoninCarrier`.  Gate 3U, the finite-S sign, Burnol's
identity, and `_root_.RiemannHypothesis` remain open.

## Verification

The focused source target passed in the Ubuntu-24.04 WSL2 ext4 mirror with
`3289/3289` jobs.  The import-facing audit passed with the declaration using
exactly

```text
[propext, Classical.choice, Quot.sound]
```

The `CCM25Concrete` aggregate passed with `3979/3979` jobs, and the full
repository build passed with `4060/4060` jobs.  No `sorry`, `admit`, or user
axiom was added.
