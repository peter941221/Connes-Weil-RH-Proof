# 1532 — Prolate commutator column is an actual HS consumer

Date: 2026-09-17

The two-column interface of record 1531 still listed the prolate column as a
premise.  This record removes that premise for every bounded physical factor.

Let `A` be the committed source prolate factor and `K = A† A` the source
prolate remainder.  The all-scale theorem gives square-summability of `A` on
the named global basis.  The Hilbert--Schmidt ideal lemmas then give:

* `K` is square-summable on the global basis by bounded postcomposition with
  `A†`;
* `K J N` is square-summable on any source basis by bounded precomposition;
* `K M J N` and `M K J N` remain square-summable for arbitrary bounded `M,N`;
* their difference, followed by arbitrary bounded `D`, is square-summable.

The owning theorem
`sourceProlateCommutator_sourceBasis_normSq_summable_of_factor` formalizes
the resulting prolate commutator column.  Consequently record 1531's
two-column consumer now has only one unresolved analytic premise: the signed
Hardy-sub-identity column `((E Q E) M - M) J` for the actual physical factors.
No positivity or RH conclusion is asserted.

The corollary
`sourceSoninCommutator_sourceBasis_normSq_summable_of_hardySubId_factor`
packages this with the signed consumer of record 1531.  Its sole analytic
premise is the Hardy-sub-identity column for the actual factorization.

Owning declaration: `ConnesWeilRH.Dev.C1G8R3BoundaryOutputFactorizationBridge`.
Audit: `...BoundaryOutputFactorizationBridgeAudit`.
