# 1203 - Signed reference-budget comparison is tautological

Date: 2026-09-06.

Status: formal no-go for the reference-budget variant. RH is not claimed.

The signed residual contract from record 1202 was

```text
ICgate(ICdefect(g², W²)) ≤ -p2AggregateValue(W).
```

For every reference `W`, `p2AggregateValue(W) = ICgate(W²)` and the exact
defect identity gives

```text
ICgate(ICdefect(g², W²)) = ICgate(g²) - ICgate(W²).
```

The contract is therefore universally equivalent to `ICgate(g²) ≤ 0`; the
reference does not provide any additional budget, whether or not it is
vanishing. The signed residual remains a valid identity, but this particular
comparison is not a producer. Route 1 must now supply a direct same-owner
semi-local gate estimate or a genuinely different inequality whose right-hand
side is not exactly `-p2AggregateValue(W)`.

Evidence: `signedDefectGateResidual_iff_detectorGate_nonpos` in
`C1P2BilateralProfileExit`; focused build `p2-signed-tautology.log` completed
successfully with 3778 jobs, standard axioms only, and no `sorryAx`.
