# Route A record 2192: geometric weighted-zero shell budget

## Consumer and owner

The consumer remains the healthy `CompactLog` B5 signed same-owner `qw >= 0`
producer. The owner is the exact `sourceNontrivialZeroSet`, partitioned by
`spectralHeightShell`; no ROOT or fixed-prime owner is introduced.

## Result

The existing analytic count theorem
`spectralHeightMultiplicity_geometric_bound` gives multiplicity growth `3^n`.
Combined with the exact-shell quadratic Laplace estimate from record 2191,
the new audited theorem
`exists_geometric_spectralHeightShell_weightedZeroMeasure_bound` proves that
for some `B >= 0`, every shell obeys

```text
sum_{rho in shell(n+1)} W(F,rho)
  <= spectralMultiplicityConstant * B * (3/4)^n.
```

Thus the analytic shell series is genuinely summable with ratio `3/4`; this
is not a numerical fit or a conditional multiplicity assumption.

## Verification

Owning module: `results/20260929_a0051_module_2192.log`, exit 0.
Paired audit: `results/20260929_a0051_audit_2192.log`, exit 0. The theorem has
only `[propext, Classical.choice, Quot.sound]` and no `sorryAx`.

## Status

This removes the geometric-convergence premise but does not close the signed
producer. The next required gate is an explicit total weighted-zero constant
and a certified comparison with the selected-owner signed epsilon. If that
comparison fails, it must be recorded as a quantitative margin/no-go for this
owner and parameter set.
