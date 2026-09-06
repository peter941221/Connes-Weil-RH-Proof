# 1206 - Route 1 canonical direct-gate socket

Date: 2026-09-06.

Status: formal producer interface. RH is not claimed.

The reference-budget family is closed by records 1203 and 1205. The active
Route-1 producer is therefore packaged as the minimal data

```text
P2DirectGateProducerData g :=
  { hgate : ICgate(g.convolutionSquare) ≤ 0 }.
```

The aggregate witness adapter and the existing healthy B5 `SourceRH` consumer
are unchanged. This structure stores no `qw` conclusion and no vacuous field;
its sole field is exactly the detector-specific semi-local sign still required.
The remaining analytic work may arrive through a signed profile/range estimate,
a valid same-owner positive-trace construction, or another proof of this field.

Evidence: `P2DirectGateProducerData` and
`P2BilateralProfileAggregateWitness.of_directGateProducerData` in
`C1P2BilateralProfileExit`, audited by `C1P2BilateralProfileExitAudit`.
