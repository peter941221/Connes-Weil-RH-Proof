# 2333 — Forward-shadow Taylor-tail budget

Scope correction (record 2334): this record evaluates the auxiliary P-only
construction from 2249, not the actual selected detector. All margin ratios
below are auxiliary comparisons only; they supply no selected-owner producer
margin or Fourier certificate. See 2334_fourier_object_scope_correction.md.

The first per-node `mpmath.iv` implementation was stopped as an engineering
path: it produced no artifact and was dominated by repeated scalar interval
calls. It is not a mathematical result.

The usable 2333 probe instead reuses the 2249 forward shadows for the positive
order-34 basis tail, applies an outward first-order product budget, and sums
with `math.fsum` plus the registered `SUMCHARGE` accumulation allowance.

```text
+--------------------------------+----------------------+
| quantity                       | value                |
+--------------------------------+----------------------+
| panel width                   | 0.25                 |
| panel radius                  | 0.125                |
| tail order                    | 34                   |
| Taylor-tail proxy             | 1.133133770579e7      |
| proxy / current margin        | 6.763378563666e-6     |
+--------------------------------+----------------------+
```

The reading agrees with 2332 at displayed precision, so stored-operation
rounding does not consume the budget at this scale. This is still not a
formal directed interval certificate: the center jets, coefficient casts,
and endpoint/full-line terms remain outside the proof object.

Evidence: `scripts/routea_forward_tail_budget_2333.py` and
`results/2333_forward_tail_budget.json`.
