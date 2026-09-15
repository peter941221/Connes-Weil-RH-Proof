# 038 — R3 actual-cutoff survivor/boundary trace limit

**Authority:** supporting.

**Status:** formal ordinary-trace convergence for the ordered
survivor/visible-boundary mixed channel of the actual G8 cutoff, on the same
healthy `CompactLog` detector owner.

**Consumer:** the mixed-channel ledger component of the detector-selected
semi-local B5 readback for the selected owner and its finite visible-prime
family. The binding route ruling in [003](003_b1_b5_minimal_exit_route_selection.md)
is unchanged.

The Lean theorems
[`tendsto_ordinaryTraceAlong_g8MetricSurvivorVisibleBoundary_actualCutoff`](../../ConnesWeilRH/Dev/C1G8R3ActualCutoffSurvivorBoundaryTraceLimit.lean)
identifies the ordered limit as the same-owner detector response between the
compressed global convolutions. The theorem
`tendsto_ordinaryTraceAlong_g8MetricPairedSurvivorBoundary_actualCutoff`
combines both orientations and gives twice the real part of that limit. The
proof uses the fixed three-branch Hilbert--Schmidt pair and actual-cutoff
strong-sandwich trace transfer.
See [proof record 1483](../proofs/1483_r3_actual_cutoff_survivor_boundary_trace_limit.md)
and prior [record 037](037_r3_actual_cutoff_survivor_boundary_pair.md).

This is the mixed channel only. Record 1484 now rewrites each diagonal channel
at finite cutoff as a same-basis detector-root energy; it does not supply the
uniform energy estimates or limits. The total four-channel readback, signed
remainder decay, `qw` identification, endpoint/P2 sign obligations, detector
semi-local positivity, C3, and RH remain open. These are formal Lean results,
not literature claims or numerical candidates.
