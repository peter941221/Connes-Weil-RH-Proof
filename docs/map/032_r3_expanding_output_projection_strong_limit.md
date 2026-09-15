# 032 — R3 expanding output-projection strong limit

**Authority:** supporting.

**Status:** expanding interval projections and the support-owned physical G8
factor/source compression are formally strongly convergent. Uniform doubled
bounds and trace/readback remain open.

**Consumer:** the literal output-window factor in the leakage/source cross
channel of the healthy-`CompactLog`, detector-selected B5 G8 route. The
downstream sign consumer remains
`0 <= C1SameOwnerWeil.qw g` for the tower-selected detector.

The formal theorem
[`tendsto_kernelIntervalProjection_symmetric_apply`](../../ConnesWeilRH/Dev/C1G8R3OutputProjectionStrongLimit.lean)
proves strong convergence of the projection onto `[-n,n]` to the identity.
It uses the projection's AE indicator formula, finite L2 mass of the squared
input, and monotone convergence of the complementary tails. Its paired audit
has only the three standard axioms; see
[proof record 1477](../proofs/1477_r3_expanding_output_projection_strong_limit.md).

The physical factor is `P_n F_g`, with `P_n` this interval projection and
`F_g` the fixed global convolution. Record 1478 now composes the projection
limit through `F_g` and the source inclusion, including the adjoint-side
strong limit, for the actual support-owned cutoff sequence. The uniformly
bounded doubled source limit and source-column summability needed for trace
transfer remain open; see supporting record
[033](033_r3_physical_cutoff_factor_strong_limit.md). This record does not
assert any `qw` sign, positivity, C3, or RH.

No binding route ruling changes.
