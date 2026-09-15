# 031 — R3 strong-sandwich trace transfer

**Status:** formal conditional HS-pair trace transfer; G8 cutoff/readback remains open.

**Consumer:** the same-owner detector-selected healthy-`CompactLog` B5 target
`0 <= C1SameOwnerWeil.qw g`, then the existing `SourceRH` contradiction.

The generic theorem in
[`C1G8R3StrongTracePairTransfer.lean`](../../ConnesWeilRH/Dev/C1G8R3StrongTracePairTransfer.lean)
transfers ordinary trace through a uniformly bounded, pointwise-convergent
doubled cutoff when the trace owner is a fixed pair of Hilbert--Schmidt legs.
It is instantiated for the existing three-branch `sourceBandGramResponse`
pair. See [proof record 1476](../proofs/1476_r3_strong_pair_sandwich_trace_transfer.md)
for the formal evidence and exact assumptions.

This gives P1 a callable conditional trace-continuity step. It does not prove
those strong-limit hypotheses for the literal G8 window factor, whose
finite-window pair varies around `g8AdjointShearGram` on the ambient carrier.
The G8 cutoff/source compatibility, same-owner `qw` readback, detector
semi-local sign, C3, and RH remain open. This record does not change the
binding route ruling in
[003](003_b1_b5_minimal_exit_route_selection.md).
