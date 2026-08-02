# Proof 703: Full-Boundary Injectivity Guard

## What is established

`SelectedWeilSquareOwner` stores a compact log root and a support bound for
its convolution square.  It does not store root nondegeneracy or a
finite-window uniqueness theorem.

Lean makes the missing condition explicit:

```text
g.test = 0
  -> fullBoundaryRootFactor g a c = 0
```

Consequently, if the source Sonin carrier contains a nonzero vector, the
Proof 702 premise

```text
fullBoundaryRootFactor owner.sourceTest a c
    (cc20GlobalLogTranslation (Real.log lambda)
      (sourceInclusion lambda y)) = 0
  -> y = 0
```

is false for a zero `sourceTest`.

The same module also proves the usable converse at the arithmetic level:

```text
finitePrimeTerm owner n != 0 -> owner.sourceTest.test != 0
p in (ofSelectedOwner owner).visiblePrimes
  -> owner.sourceTest.test != 0.
```

The first implication expands the genuine convolution square; the second uses
the canonical prime-power family derived from the same selected owner.  This
supplies root nondegeneracy whenever a selected arithmetic atom is already
known to survive.  It does not supply uniqueness of the full boundary factor
on the translated Sonin carrier.

## Why this matters

Support inclusion, compactness, positivity, and Hilbert--Schmidt structure do
not imply injectivity.  The route must provide a genuine nondegenerate root
and a finite-window uniqueness theorem on the translated Sonin carrier, or
strengthen the owner contract with those facts.  This guard does not change
the public owner structure and does not prove Gate 3U.

The guard is a structural obstruction, not a no-go theorem for the intended
nonzero Yoshida owner.  It only prevents treating the current generic owner
fields as an injectivity producer.

## Verification

The focused source and audit passed in Ubuntu-24.04 WSL2 with `3289` jobs.
The `CCM25Concrete` aggregate passed with `3976` jobs, and the full repository
build passed with `4057` jobs.  The guard adds no user axiom, `sorry`, or
`admit`.

The audited declarations use exactly:

```text
[propext, Classical.choice, Quot.sound]
```
