# 1199 - Route 1 reference-residual aggregate consumer

Date: 2026-09-06.

Status: formal consumer contract.  RH is not claimed.

Consumer: `P2BilateralProfileAggregateWitness` on the healthy `CompactLog`
owner.

The theorem
`P2BilateralProfileAggregateWitness.of_visibleProfileReferenceResidual`
consumes two triple-vanishing owners `g` and `W`, together with:

1. bilateral profile matching on the union of their visible-prime log points;
2. the signed Archimedean residual bound

   ```text
   arch(g²) - arch(W²) ≤ -p2AggregateValue(W).
   ```

Using record 1198's exact residual identity, it produces the aggregate
inequality `p2AggregateValue g ≤ 0`, then packages it into the existing P2
aggregate witness without storing `qw ≥ 0` as source data.

This is the minimal reference-owner route-1 producer shape currently exposed
by the formalization.  It is not yet instantiated for `narrowArchRoot` or for
the pinned orbit correction: the missing mathematics is precisely the visible
profile matching/signed residual proof.

Evidence: `C1P2BilateralProfileExit.lean` and its paired audit.  Focused
build `p2-reference-residual-consumer.log` completed successfully with the
standard axioms only and zero `sorryAx`.
