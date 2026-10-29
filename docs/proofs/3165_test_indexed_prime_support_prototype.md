# 3165: test-indexed finite-prime support prototype

Date: 2026-10-29
Status: development prototype; no public API change.

## Result

Added `ConnesWeilRH/Dev/C1TestIndexedPrimeSupport3165.lean` with a small
Route A development interface:

```text
TestIndexedFinitePrimeSupport
  globalIndexSet       : CompactLogTest -> Finset Nat
  restrictedIndexSet   : Real -> CompactLogTest -> Finset Nat
  globalMem_iff        : visible prime-power characterization
  restrictedMem_iff    : global membership plus lambda cutoff
```

The canonical instance uses the existing
`C1SameOwnerWeil.globalPrimeIndexSet F` and filters it for the restricted set.
No fixed `SourceWeilFormData` or `WeilFormSymbols` field was changed.

## Existing proofs reused

- `C1SameOwnerWeil.mem_globalPrimeIndexSet_iff` proves exact global membership.
- `C1SameOwnerWeil.finitePrimeTermComplex_nonzero_primePower` proves every
  visible finite-prime index is a prime power.
- `C1SameOwnerWeil.index_lt_globalIndexBound` supplies the finite range from
  compact support.
- The restricted readback is proved by the existing global characterization
  plus `1 < n` and `(n : Real) <= lambda^2`.

## Verification

```text
lake env lean ConnesWeilRH/Dev/C1TestIndexedPrimeSupport3165.lean

[propext, Classical.choice, Quot.sound]
[propext, Classical.choice, Quot.sound]
[propext, Classical.choice, Quot.sound]
```

The prototype is axiom-clean and contains no `sorryAx`. It is not yet wired
into the CCM25 constructor or Route A consumer; that wiring is the public API
decision identified in record 3164.

## Consequence

The proposed dynamic support boundary is technically viable in the current
codebase. The next design step is to decide whether to expose this interface
as a new Route A owner API while keeping the fixed-index legacy CCM25 API
unchanged.

No root migration, SourceRH claim, or RH claim follows from this prototype.
