# 2857 Route B sharp-e0 reprice

Using the Lean-certified `[1/16,1/8]` initial exponential box from record
2856, the order-7 cell-4096 stages were regenerated. Transition width ratios
against the old Python tight targets are approximately 826, 625, 522, 497,
523, 580, 657, and 767 for slots 0 through 7.

The sharper e0 materially improves the broad-e0 reprice, but the resulting
boxes still cannot consume the old tight charge ledger. A new target ledger or
further analytic tightening is required.
