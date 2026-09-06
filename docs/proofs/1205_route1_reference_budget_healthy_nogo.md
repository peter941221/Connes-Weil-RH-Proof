# 1205 - Reference-budget contract contradicts the healthy detector

Date: 2026-09-06.

Status: formal no-go. RH is not claimed.

The universal algebraic equivalence from record 1203 combines with the formal
healthy-detector fact `qw(g) < 0`. On the same owner this gives
`ICgate(g.convolutionSquare) > 0`. Therefore no healthy detector can satisfy

```text
ICgate(ICdefect(g², W²)) ≤ -p2AggregateValue(W)
```

for any reference `W`. This closes the entire reference-budget comparison
family as a possible producer. It does not close the direct P2 obligation:
the desired result is precisely a new detector-specific proof of
`ICgate(g.convolutionSquare) ≤ 0`, which would contradict the healthy branch
and force the B5 exit.

Evidence: `not_signedDefectGateResidual_of_healthyDetectorData` in
`C1P2BilateralProfileExit`, audited by its paired audit module. The focused
build `p2-reference-budget-healthy-nogo.log` completed successfully with
3778 jobs, standard axioms only, and no `sorryAx`.
