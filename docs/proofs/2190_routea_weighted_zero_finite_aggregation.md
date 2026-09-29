# 2190 — Route-A finite weighted-zero aggregation

Date: 2026-09-29  
Status: `FORMAL SMALLER OBLIGATION`; no producer closure.

The factor split of 2189 is now aggregated on the exact finite source-zero
owner. For a finite `S`, pointwise bounds

```text
xiMultiplicity rho <= Mmult
||laplaceAt F (rho - 1/2)|| <= Meval
```

give the audited finite-sum bound

```text
sum rho in S, weightedZeroMeasure F rho
  <= card(S) * (Mmult * Meval).
```

The owning module and paired audit pass with the standard three axioms and no
`sorryAx`. This does not provide the shell cardinality, multiplicity, or
transform enclosure bounds; it packages exactly how those future bounds enter
`B_zm`.

Evidence: `results/20260929_a0051_module_2190.log` and
`results/20260929_a0051_audit_2190.log` in the WSL mirror.
