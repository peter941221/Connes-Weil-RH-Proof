# 1204 - Route 1 residual identity admits a non-vanishing reference

Date: 2026-09-06.

Status: formal interface correction. RH is not claimed.

The identity

```text
p2AggregateValue(g) - p2AggregateValue(W)
  = ICgate(ICdefect(g², W²))
```

uses only the unconditional readback
`p2AggregateValue(F) = ICgate(F.convolutionSquare)` and the exact singleton
defect-gate subtraction law. It does not require `W` to satisfy the healthy
triple-vanishing condition. Therefore a useful reference may be non-vanishing
and may carry an independently certified aggregate value.

Record 1203 strengthens this diagnosis: the reference-budget inequality
cancels to the direct detector-gate target even for non-vanishing `W`. A
non-vanishing reference remains available for other comparison identities, but
it cannot make that particular one-sided bound easier.

Evidence: `p2AggregateValue_sub_eq_defectGate` in `C1P2BilateralProfile`;
`p2-nonvanishing-reference-2.log` completed successfully with 3778 jobs,
standard axioms only, and no `sorryAx`.
