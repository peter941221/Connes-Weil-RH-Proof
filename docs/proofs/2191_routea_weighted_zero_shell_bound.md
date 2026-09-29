# Route A record 2191: exact-shell weighted-zero bound

## Consumer and obligation

Consumer: the healthy `CompactLog` B5 producer, whose remaining analytic
premise is a signed same-owner `qw >= 0` margin. Owner: the exact
`sourceNontrivialZeroSet`, grouped by `spectralHeightShell`; no ROOT or fixed-
prime replacement is used. This brick removes the shell-level packaging
premise: a weighted-zero sum must be bounded by analytic multiplicity mass
before the finite prefix/tail split can be priced.

## Formal result

`exists_spectralHeightShell_weightedZeroMeasure_bound` is proved in
`C1RouteAWeightedZeroMeasure.lean` and audited in its paired audit file. It
uses the existing quadratic dyadic Laplace estimate and proves that there is
`B >= 0` such that, for every `n`,

```text
sum_{rho in shell(n+1)} W(F,rho)
  <= spectralHeightMultiplicity(n+1) * (B / (2^n)^2).
```

The finite sum is over the exact source-zero owner; the pointwise Laplace
bound is applied after inserting the shell-membership proof.

## Verification

Owning module: `results/20260929_a0051_module_2191_rerun.log`, exit 0.
Paired audit: `results/20260929_a0051_audit_2191.log`, exit 0; the new theorem
has only `[propext, Classical.choice, Quot.sound]` and no `sorryAx`.

## Status

This is a strictly smaller quantitative obligation, not producer closure.
The next gate is an explicit bound on
` spectralHeightMultiplicity (n+1)` (or its finite-height certificate), then
the resulting geometric shell constant must be compared with the signed
epsilon budget.
