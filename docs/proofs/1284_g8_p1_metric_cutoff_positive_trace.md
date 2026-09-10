# 1284 — G8 P1 metric cutoff nonnegative trace

Date: 2026-09-10.

Status: FORMAL Lean fact. This remains a fixed-cutoff statement and does not
assert finite-prime readback, endpoint convergence, P2 remainder decay, `qw`,
or RH.

Using the positivity theorem for the literal metric operator and its
same-owner trace-class certificate, the import-facing leaf proves

```text
0 ≤ Re ordinaryTraceAlong sourceBasis
      (g8PhysicalMetricCutoffOperator ... n).
```

The proof expands the ordinary trace into its diagonal sum, applies
`Complex.re_tsum`, and uses pointwise positivity of the detector conjugation.
A local alias keeps the large cutoff operator from causing the kernel timeout
seen in the original wrapper attempt.

Verification: `1294_g8_p1_metric_positive_trace_retry.log`, green owning/Audit
build (3926 jobs), zero `error:`/`sorryAx`, standard three axioms only.
