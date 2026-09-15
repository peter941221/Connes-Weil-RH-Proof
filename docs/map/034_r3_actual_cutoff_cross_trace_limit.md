# 034 — R3 actual cutoff cross-channel trace limit

**Authority:** supporting.

**Status:** the actual source-compressed physical cutoff is uniformly bounded;
its doubled product converges strongly. The literal leakage/source cross
channel pair and the same-owner signed source-remainder sandwich have formal
ordinary-trace limits. The remaining coframe channels and full metric
readback to `qw` remain open.

**Consumer:** the actual G8 leakage/source-cross channel on the healthy
`CompactLog` owner, downstream of which the active B5 consumer remains
`0 <= C1SameOwnerWeil.qw g` for the tower-selected detector.

Record [1479](../proofs/1479_r3_actual_cutoff_cross_trace_limit.md) applies the
uniformly bounded strong-sandwich trace transfer from record 1476 to the real
window sequence. The cutoff is the source compression of the reflected output
projection followed by the fixed global detector convolution. Its limit is
the same-detector source-band response between two compressed global
convolutions, with the exact leakage/source orientation retained.

Record [1481](../proofs/1481_r3_actual_cutoff_paired_cross_trace_limit.md)
closes the reverse ordered channel by adjoint symmetry and proves that the
two cross traces sum to twice the real part of the forward limit. Record
[1480](../proofs/1480_r3_actual_cutoff_signed_remainder_limit.md) separately
proves convergence of the signed same-owner source-remainder response through
the same cutoff. These results do not identify the full ledger with `qw`; the
survivor/boundary coframe channels and the complete readback remainder remain
unresolved, and `G8SameOwnerReadbackData` has not been constructed. The binding
healthy-`CompactLog`, B5 route is unchanged.
