# 2442 — Route A profile exponential interval propagation

Date: 2026-10-02.

Lean proves the monotone interval propagation used by the bump evaluator:
for `0 < qlo ≤ q ≤ qhi`, the value `exp(-30/q)` lies between the endpoint
evaluations `exp(-30/qlo)` and `exp(-30/qhi)`.

This is the analytic core of the positive-`q` bump branch.  It does not certify
the MPFR endpoint values or the construction of the `q` interval itself.
