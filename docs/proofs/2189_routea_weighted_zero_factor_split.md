# 2189 — Route-A weighted-zero factor split

Date: 2026-09-29  
Status: `FORMAL SMALLER OBLIGATION`; no producer closure.

## Landed theorem

For the exact source-zero owner and any nonnegative bounds `Mmult` and
`Meval`, the paired audited theorem proves

```text
xiMultiplicity rho <= Mmult
||laplaceAt F (rho - 1/2)|| <= Meval
  -> weightedZeroMeasure F rho <= Mmult * Meval.
```

This separates analytic multiplicity inflation from transform/evaluation
enclosure inflation. It does not replace the source-zero subtype, change the
selected test, or assume the desired sign.

## Verification

- owning module refresh: `results/20260929_a0051_force_module_2189c.log`;
- paired audit: `results/20260929_a0051_audit_2189.log`;
- new audited leaf axioms: `[propext, Classical.choice, Quot.sound]`;
- no `sorryAx` and no producer/RH conclusion.

## Next quantitative target

Aggregate this pointwise factor over the exact finite shell prefix, with a
cardinality/multiplicity bound and an outward transform enclosure. The 2188
candidate stress budget supplies the diagnostic target: the combined inflation
must remain below approximately `484.82` relative to the consumer anchor.
