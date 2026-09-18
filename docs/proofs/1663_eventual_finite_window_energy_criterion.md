# 1663 - Eventual finite-window energy criterion

Date: 2026-09-19.

Status: formal conditional reduction. RH is not claimed.

## Result

The reverse-limit lemma now has an eventual form.  If the finite-window
approximants converge strongly pointwise to an operator `T`, it is enough to
bound the finite basis energy uniformly for all window indices `n >= N`.
The proof reindexes the approximants by `n + N` and applies the existing
uniform criterion; the finitely many smaller windows are irrelevant.

The source-compressed root consumer now exports the corresponding theorem for
the actual approximants

```text
J† P_n C J
```

and accepts an explicit natural threshold `N`.  Thus the remaining producer
obligation is precisely a radius-uniform finite-set bound after a support
threshold.  Record 1662 supplies square-summability for each individual
window, but not this collective bound.

## Lean evidence

Declarations:

```text
summable_normSq_of_eventual_uniform_finite_window_energy
sourceCompressedRoot_squareSum_of_eventual_uniform_finite_window_energy
```

Build log: `1663_source_eventual_fix`.

The owning module and audit both completed successfully (3962 jobs), with no
`error:`, no `sorryAx`, and only the standard axioms
`[propext, Classical.choice, Quot.sound]`.

## Boundary

This is a reduction, not the missing estimate.  The active healthy-
`CompactLog` B5 route still needs the source-compressed collective radial-tail
bound; no ROOT-window density lift, universal B1 claim, or RH conclusion is
introduced.
