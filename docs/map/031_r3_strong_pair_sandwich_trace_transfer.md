# 031 — R3 strong-sandwich trace transfer

**Status:** the conditional transfer is formal and applies to the actual G8
leakage/source cross-channel pair; full G8 readback remains open.

**Consumer:** the same-owner detector-selected healthy-`CompactLog` B5 target
`0 <= C1SameOwnerWeil.qw g`, then the existing `SourceRH` contradiction.

The generic theorem in
[`C1G8R3StrongTracePairTransfer.lean`](../../ConnesWeilRH/Dev/C1G8R3StrongTracePairTransfer.lean)
transfers ordinary trace through a uniformly bounded, pointwise-convergent
doubled cutoff when the trace owner is a fixed pair of Hilbert--Schmidt legs.
It is instantiated for the existing three-branch `sourceBandGramResponse`
pair. See [proof record 1476](../proofs/1476_r3_strong_pair_sandwich_trace_transfer.md)
for the formal evidence and exact assumptions.

Record [1479](../proofs/1479_r3_actual_cutoff_cross_trace_limit.md) proves the
uniform bound and doubled strong limit for the actual source compression, then
uses this fixed pair to obtain ordinary-trace convergence for the ordered
leakage/source cross channel. Record
[1481](../proofs/1481_r3_actual_cutoff_paired_cross_trace_limit.md) closes the
reverse orientation by adjoint symmetry and proves the real paired limit. This
does not give the full G8 metric trace-to-`qw` readback; the three other
survivor/boundary coframe channels, signed remainder decay/readback, detector
semi-local sign, C3, and RH remain open. This record does not change the
binding route ruling in [003](003_b1_b5_minimal_exit_route_selection.md).
