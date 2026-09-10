# 1277 — G8 P1 metric-channel trace owners

Date: 2026-09-10.

Status: FORMAL Lean fact. This record supplies no finite-prime equality, limit,
sign, `qw` readback, or RH claim.

The generic `g8MetricCutoffChannelPairData` packages each ordered channel

```text
C_n^* L^* W_g R C_n
```

as a concrete same-owner Hilbert--Schmidt pair with legs `L C_n` and
`W_g R C_n`. Lean proves its trace product is exactly the named channel and
therefore each of the four channels from record 1276 is independently
`TraceClass` on the source basis. The proof uses bounded postcomposition of the
already summable literal cutoff leg; it introduces no owner change or external
subtraction.

The aggregate visible-place boundary is still indexed by the deduplicated
`family.visiblePrimes`, while the existing arithmetic scalar is indexed by
prime powers. The next P1 obligation remains the aggregate same-owner trace
comparison, not termwise reuse of the uncut readback.

Verification: `1277_g8_p1_metric_channel_pairs_retry2.log`, green owning/Audit
build (3925 jobs), zero `error:`/`sorryAx`, and standard three axioms only.
