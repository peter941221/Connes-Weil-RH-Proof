# Record 1149 - exact visible-prime point matching

Date: 2026-09-06.

Status: FORMAL consumer brick. Consumer: the healthy `CompactLog`, B5-shaped
Line-C P2 producer. No sign theorem and no RH claim.

## Landed theorem

`ConnesWeilRH/Dev/C1P2PrimePointMatching.lean` defines
`PrimePointMatch F G`, requiring equality of the two square-owner test values
at both real points `± log n` for every index in
`globalPrimeIndexSet F ∪ globalPrimeIndexSet G`.

The theorem
`finitePrimeSum_eq_of_primePointMatch` proves exactly

```text
PrimePointMatch F G
  -> finitePrimeSum F = finitePrimeSum G.
```

The proof enlarges both finite visible sets to their union. Terms outside an
owner's own visible set vanish by the formal characterization
`mem_globalPrimeIndexSet_iff`; terms on the union agree by unfolding
`finitePrimeTermComplex`.

## Why this matters for Line C

For the one-window defect, take
`F = g.convolutionSquare` and `G = W.convolutionSquare`. A future correction
producer that establishes `PrimePointMatch F G` removes the entire finite-prime
part of the exact identity

```text
ICgate(defect) = qw(W) - qw(g)
```

without a triangle estimate. The remaining obligation is then an
archimedean/correction cancellation on the same owner.

This does not yet construct the matching correction. The existing
`exists_residualWindow_correction` theorem interpolates finitely many Mellin
values, whereas `PrimePointMatch` asks for real point values of the
convolution squares. Establishing that mixed interpolation, or replacing it
by a low-rank residual identity, is the next genuine analytic producer task.

## Verification

Owning and audit modules build with the resource-aware runner:
`Build completed successfully (3477 jobs)`, zero `error:` lines. The audit
prints exactly `[propext, Classical.choice, Quot.sound]` for the headline
theorem; no `sorryAx` occurs.
