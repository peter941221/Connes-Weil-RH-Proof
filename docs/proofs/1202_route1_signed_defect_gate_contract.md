# 1202 - Route 1 signed defect-gate contract

Date: 2026-09-06.

Status: formal interface and B5 consumer. RH is not claimed.

For any two `CompactLog` owners `g` and `W`, the exact same-owner identity is

```text
p2AggregateValue(g) - p2AggregateValue(W)
  = ICgate(ICdefect(g², W²)).
```

Consequently the candidate producer contract can be stated without any
profile matching:

```text
ICgate(ICdefect(g², W²)) ≤ -p2AggregateValue(W).
```

With the detector's triple-vanishing hypothesis, this immediately gives
`p2AggregateValue(g) ≤ 0`, hence `qw(g) ≥ 0`, and the healthy B5 contradiction
consumer yields `SourceRH` when supplied for every right-oriented off-line
zero. The finite-prime contribution remains signed and is owned by the same
`ICdefect`; no density lift, universal B1 statement, or normalized additive
owner is introduced.

Evidence: `p2AggregateValue_sub_eq_defectGate` in
`C1P2BilateralProfile`,
`P2BilateralProfileAggregateWitness.of_signedDefectGateResidual` and
`sourceRH_of_pinnedOrbitDetector_p2SignedDefectGateResidual` in
`C1P2BilateralProfileExit`. The focused audit build
`p2-signed-consumer-2.log` completed successfully with 3778 jobs, standard
axioms only, and no `sorryAx`.
