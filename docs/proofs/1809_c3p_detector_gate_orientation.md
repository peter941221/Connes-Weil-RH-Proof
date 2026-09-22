# 1809 — C3' detector gate orientation

Date: 2026-09-22.

Status: FORMAL bridge complete. The C3' semi-local sign and RH remain open.

## Result

For every `HealthyYoshidaDetectorData rho g`, the existing strict positive
healthy local sum, together with the triple-vanishing readback, implies

```text
0 < ICgate g.convolutionSquare.
```

The Lean declaration is
`ICgate_pos_of_healthyDetectorData` in
`C1P2EvenOddGateDecomposition.lean`.

## Route consequence

This is a same-owner orientation fact, not an added hypothesis. It shows that
the selected detector cannot itself supply the negative diagonal in the
even/odd opposite-sign branch. Any useful negative parity component must be a
separately constructed test, and its three-node vanishing and detection at the
hypothetical zero must be preserved before the two-span consumer can feed B5.

## Verification

Focused build log:
`/home/peter/rh/build-logs/1809_detector_gate_positive.log`

The build completed successfully with 3807 jobs, zero `error:` lines, zero
`sorryAx`, and only `[propext, Classical.choice, Quot.sound]` in the audit.
