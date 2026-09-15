# 1479 — R3 actual cutoff cross-channel trace limit

**Status:** formal convergence for the literal leakage/source cross channel;
full G8 readback and the trace-to-`qw` limit remain open.

**Consumer:** the actual G8 leakage/source-cross channel on the selected
healthy-`CompactLog` owner. The downstream B5 sign consumer remains
`0 <= C1SameOwnerWeil.qw g` for the tower-selected detector.

The paired leaf
[`C1G8R3ActualCutoffCrossTraceLimit.lean`](../../ConnesWeilRH/Dev/C1G8R3ActualCutoffCrossTraceLimit.lean)
proves the following chain.

1. Each reflected output-window projection is a contraction, and the source
   inclusion is a contraction. Therefore the actual source-compressed finite
   factor has operator norm at most the norm of the fixed global detector
   convolution.
2. The source-compressed factors and their adjoints converge strongly by the
   actual physical-cutoff theorem from record 1478. A general lemma combines
   these limits with the uniform bound to give strong convergence of the
   doubled products `C_n * C_n†`.
3. The finite leakage/source cross channel is exactly
   `C_n† * (-sourceBandGramResponse†) * C_n`. The fixed source three-branch
   Hilbert--Schmidt pair owns the middle response, so record 1476's dominated
   trace transfer proves convergence of the ordinary traces.

The limit is explicitly the same-detector source response between two copies
of the compressed global convolution `J† * F_g * J`. This is only one ordered
channel of the finite G8 metric ledger. The theorem does not identify its limit
with `qw g`, prove convergence of the other metric channels or the analytic
remainder, or construct `G8SameOwnerReadbackData`. The B5 route and the RH
status do not change.

The paired audit checks the general doubled-product lemma, the uniform bound,
both strong-limit interfaces, and the actual trace theorem. Acceptance log
`0915_actual_cutoff_cross_try7.log` reports `Build completed successfully
(3955 jobs)`, zero `error:` lines, zero `sorryAx`, and five occurrences of
the standard audit terminator `Quot.sound]`.
