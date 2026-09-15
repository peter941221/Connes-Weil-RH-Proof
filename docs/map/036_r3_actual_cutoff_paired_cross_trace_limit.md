# 036 — R3 actual-cutoff paired cross-channel trace limit

**Authority:** supporting.

**Status:** both ordered actual G8 leakage/source cross channels and their
real paired ordinary trace have formal limits. The other coframe channels and
the full readback to `qw` remain open.

**Consumer:** the paired leakage/source cross part of the actual cutoff metric
ledger on the healthy `CompactLog` owner. The active B5 consumer remains
`0 <= C1SameOwnerWeil.qw g` for the tower-selected detector.

Record [1481](../proofs/1481_r3_actual_cutoff_paired_cross_trace_limit.md)
proves that the source/leakage orientation is the adjoint of the
leakage/source orientation, since the detector Gram is self-adjoint. The
same-basis ordinary trace of the reverse orientation is therefore the
conjugate of the forward trace. Combining both limits gives the real paired
limit `2 * Re(forward limit)` for the actual source-compressed physical G8
cutoff.

This closes the cross pair, not the separate survivor/boundary four-channel
coframe ledger. The three remaining coframe channels, remainder decay and
full-readback identity, `G8SameOwnerReadbackData`, the trace-to-`qw`
identification, the detector semi-local sign, C3, and RH remain open. The
binding route in [003](003_b1_b5_minimal_exit_route_selection.md) is unchanged.
