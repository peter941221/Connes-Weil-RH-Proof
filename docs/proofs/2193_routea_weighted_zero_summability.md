# Route A record 2193: actual-owner weighted-zero summability

The exact selected source-zero owner now has an unconditional formal
summability theorem:

```text
weightedZeroMeasure_summable_of_existing_xi_growth F :
  Summable (weightedZeroMeasure F)
```

It instantiates the already proved multiplicity growth
`spectralHeightMultiplicity_geometric_bound` with `q = 3 < 4`, using the
quadratic vertical Laplace decay. The paired audit reports only
`[propext, Classical.choice, Quot.sound]` and no `sorryAx`.

Owning module: `results/20260929_a0051_module_2193_rerun.log`, exit 0.
Audit: `results/20260929_a0051_audit_2193.log`, exit 0.

This closes convergence of the actual weighted-zero measure, but not its
smallness relative to the selected-owner signed epsilon. The remaining live
gate is an explicit finite prefix/tail numerical certificate and its signed
comparison.
