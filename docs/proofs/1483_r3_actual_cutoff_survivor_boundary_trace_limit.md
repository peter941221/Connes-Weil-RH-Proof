# 1483 — Actual-cutoff survivor/boundary trace limit

Date: 2026-09-15.

Status: formal same-owner mixed-channel trace convergence. This is one
component of the G8 cutoff ledger, not the complete `qw` readback.

## Consumer and result

The consumer is the detector-selected semi-local B5 producer on the healthy
`CompactLog` owner, specifically the G8 metric ledger for the same
`SelectedWeilSquareOwner` and its finite visible-prime family. The new paired
Dev leaf
[`C1G8R3ActualCutoffSurvivorBoundaryTraceLimit.lean`](../../ConnesWeilRH/Dev/C1G8R3ActualCutoffSurvivorBoundaryTraceLimit.lean)
proves that the actual source-compressed physical cutoff's ordered
survivor/visible-boundary channel has an ordinary-trace limit. Its limit is
the same-owner source response between the compressed global convolutions:

```text
trace(C_n† S† D B C_n) -> trace(C∞† S† D B C∞)
```

Here `S` and `B` are the survivor and visible-boundary coframes, `D` is the
selected detector operator, and `C_n` is the literal actual cutoff. This is
proved using the empty polar frame identity, exact survivor/boundary
orthogonality against the source Sonin projection, the existing fixed
three-branch Hilbert--Schmidt pair, and the strong-sandwich trace-transfer
theorem. It retains the same detector owner throughout.

The paired audit prints the standard axioms for
`g8MetricSurvivorBoundaryFixedPairData_traceProduct_eq` and
`tendsto_ordinaryTraceAlong_g8MetricSurvivorVisibleBoundary_actualCutoff`,
and `tendsto_ordinaryTraceAlong_g8MetricPairedSurvivorBoundary_actualCutoff`.
The last theorem combines both orientations into one real sequence with limit
twice the real part of the ordered limit. Acceptance log:
`build-logs/1502_g8_sb_trace_pair_try2.log`;
`Build completed successfully (3960 jobs)`, zero `error:` lines, zero
`sorryAx`, and three `Quot.sound]` audit terminators.

## Boundary

This closes the limit for one ordered mixed channel; its adjoint orientation
has the conjugate limit by the already formal adjoint pairing. It does not
close either diagonal channel (survivor/survivor or boundary/boundary), sum
the complete G8 trace ledger, prove decay of the signed remainder, identify
the total limit with `qw`, or establish the required nonnegative sign. The
endpoint and P2 obligations, C3, and RH remain open. No ROOT-window density
step or universal B1 claim is used.
