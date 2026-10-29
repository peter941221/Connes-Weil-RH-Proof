# 3164: fixed-index source API versus test-indexed Route A owner

Date: 2026-10-29
Status: architecture boundary; no public API change made.

## Finding

The current source-layer API stores one prime index set inside the Weil-form
owner. Route A's live compact-log owner instead computes a finite visible prime
index set separately for each formula test.

```text
SourceWeilFormData W
  W.finitePrime.globalPrimeIndexSet : Finset Nat
  W.psi F = pole F - arch F - sum over W.globalPrimeIndexSet

C1SameOwnerWeil
  globalPrimeIndexSet F : Finset Nat
  finitePrimeSum F = sum over globalPrimeIndexSet F
```

These are different ownership models. The first requires a fixed superset of
all visible primes for every test. The second uses the actual compact support of
that test to produce a finite set.

## Source evidence

- `ConnesWeilRH/Basic.lean:43-49` defines `WeilFormSymbols.globalPrimeIndexSet`
  as one `Finset Nat`, independent of `F`.
- `ConnesWeilRH/Basic.lean:70-78` defines the global finite-prime sum using
  that fixed set.
- `ConnesWeilRH/Source/AnalyticCore.lean:7832-7848` repeats the same fixed-set
  design in `SourceWeilFormData.psi`.
- `ConnesWeilRH/Source/AnalyticCore.lean:7867-7873` exports the fixed source
  support directly into `toWeilFormSymbols`.
- `ConnesWeilRH/Dev/C1SameOwnerWeil.lean:145-162` defines the Route A owner’s
  `globalPrimeIndexSet (F : CompactLogTest)` from `supportRadius F` and sums
  finite-prime terms over that test-specific set.
- `ConnesWeilRH/Dev/C1SameOwnerWeil.lean:83-118` proves the support-radius
  mechanism: a visible finite-prime term bounds `abs(log n)` by the support
  radius, which makes the per-test index set finite.

## Why the existing producer contract cannot bridge this

`SourceWeilFormData.IndexedFinitePrimeProducer` was intentionally added at the
fixed-`W` boundary. Its derived certificates must ultimately prove visibility
for every arbitrary convolution against `W.globalPrimeIndexSet` and the fixed
restricted sets. Record 3163 gives a formal contradiction for the current
common-only concrete owner: an arbitrary pair sees prime `3`, while the common
bump does not.

Therefore this is not solved by adding more common-pair certificates. The
missing invariant is either:

```text
all arbitrary source tests share one finite support set
```

or a change to a test-indexed source API.

## Decision boundary

Changing `WeilFormSymbols`, `SourceWeilFormData`, the CCM25 constructor input,
or downstream consumers is a public architecture/API change. Per project rules,
that change requires an explicit decision before editing.

Recommended direction: preserve the current fixed-index API for legacy CCM25
consumers and add a separate test-indexed Route A owner interface. This keeps
compact-support finiteness where it is proved and avoids pretending that the
common bump is a universal support witness.

Alternative: require a single finite global support envelope for all Route A
formula tests. This is simpler at the API level, but it is stronger than the
existing support-radius theorem and likely incompatible with arbitrary
compact-support detectors.

No root migration, SourceRH claim, or RH claim follows from this record.
