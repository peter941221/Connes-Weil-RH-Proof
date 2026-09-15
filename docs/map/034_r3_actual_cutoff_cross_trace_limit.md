# 034 — R3 actual cutoff cross-channel trace limit

**Authority:** supporting.

**Status:** the actual source-compressed physical cutoff is uniformly bounded;
its doubled product converges strongly, and the ordinary trace of the literal
G8 leakage/source cross channel converges. The full metric readback to `qw`
remains open.

**Consumer:** the actual G8 leakage/source-cross channel on the healthy
`CompactLog` owner, downstream of which the active B5 consumer remains
`0 <= C1SameOwnerWeil.qw g` for the tower-selected detector.

Record [1479](../proofs/1479_r3_actual_cutoff_cross_trace_limit.md) applies the
uniformly bounded strong-sandwich trace transfer from record 1476 to the real
window sequence. The cutoff is the source compression of the reflected output
projection followed by the fixed global detector convolution. Its limit is
the same-detector source-band response between two compressed global
convolutions, with the exact leakage/source orientation retained.

This closes the ordinary-trace limit for that one ordered channel. It does not
identify the result with `qw`, supply the other terms in the four-channel G8
metric ledger, prove the remainder limit, or construct
`G8SameOwnerReadbackData`. The binding healthy-`CompactLog`, B5 route is
unchanged.
