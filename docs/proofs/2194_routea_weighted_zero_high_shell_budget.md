# Route A record 2194: explicit high-shell weighted-zero budget

The exact-owner shell estimates from 2192 now assemble into the scalar tail
bound

```text
∑ n, ∑ rho ∈ spectralHeightShell (n+1), W(F,rho)
  <= 4 * spectralMultiplicityConstant * B
```

for some `B >= 0`. The factor `4` is the exact sum of the geometric ratio
`(3/4)^n`; shell zero is intentionally excluded and remains a finite prefix
term in the producer.

The theorem is proved in `C1RouteAWeightedZeroMeasure.lean` and checked by the
paired audit. Owning module:
`results/20260929_a0051_module_2194_pass2.log`, exit 0. Audit:
`results/20260929_a0051_audit_2194.log`, exit 0. The audited theorem has only
`[propext, Classical.choice, Quot.sound]` and no `sorryAx`.

This is a strict quantitative reduction, not a producer GO: the constant `B`
still comes from the existing transform enclosure and must be compared with
the selected-owner signed epsilon together with the finite shell-zero prefix.
