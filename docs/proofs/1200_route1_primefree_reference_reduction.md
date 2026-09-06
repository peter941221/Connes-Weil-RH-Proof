# 1200 - Route 1 prime-free reference reduction

Date: 2026-09-06.

Status: formal reduction.  RH is not claimed.

If a reference square `W.convolutionSquare` is supported in
`(-log 2, log 2)`, its finite-prime sum is formally zero.  If the pinned
detector square `g.convolutionSquare` matches that reference in bilateral
profile on the union of visible-prime log points, then the exact finite-prime
matching theorem transfers the zero sum to `g`:

```lean
finitePrimeSum g.convolutionSquare = 0
```

Consequently:

```lean
p2AggregateValue g = archimedeanTerm g.convolutionSquare
```

The reference candidates `primeFreePlateau` and `narrowArchRoot` have the
required prime-free support shape; the latter also has the existing strict
negative `ICgate` certificate.  This record does not prove the pinned detector
profile matching or the detector Archimedean sign.  It identifies the exact
remaining route-1 target under the prime-free-reference specialization.

Evidence: `C1P2BilateralProfile.lean` and its paired audit.  Focused build
`p2-primefree-reference.log` completed successfully with standard axioms only
and zero `sorryAx`.
