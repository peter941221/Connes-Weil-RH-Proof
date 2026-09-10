# 1283 — G8 P1 metric cutoff trace-class owner

Date: 2026-09-10.

Status: FORMAL Lean fact. No finite-prime scalar comparison, cutoff limit,
P2 remainder decay, `qw` readback, or RH conclusion is made.

The four-channel expansion of the literal metric operator supplies independent
Hilbert–Schmidt owners for survivor/survivor, survivor/boundary,
boundary/survivor, and boundary/boundary.  Closure under addition therefore
proves

```text
IsTraceClassAlong sourceBasis (g8PhysicalMetricCutoffOperator_n).
```

This packages the fixed-cutoff positivity from record 1282 with an actual
ordinary-trace owner on the same source carrier.  The attempted direct
nonnegative-real-trace wrapper was not retained because elaboration hit a
deterministic kernel timeout; the underlying positivity and trace-class facts
are both independently audited.

Verification: `1292_g8_p1_metric_traceclass_green.log`, green owning/Audit
build (3925 jobs), zero `error:`/`sorryAx`, standard three axioms only.
