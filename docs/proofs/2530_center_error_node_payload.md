# Record 2530 — center-plus-error node payload

Date: 2026-10-03.

Record 2530 materializes the viable part of record 2528 as 2561 per-node
rows for each endpoint sign. For every node it stores:

```text
center_norm        = norm of the 30-family midpoint sum
coefficient_error  = sum of the 2338 box-radius charges after the bump
weight             = exp(sigma * x)
weighted_upper     = weight * (center_norm + coefficient_error)
```

The weighted upper is also exported as an upward-rounded binary64 rational.
The exact rational trapezoid sum of those exported node values is:

```text
sigma = -1/2    2.686887376406492 (binary64 display)
sigma = +1/2    2.675211462945179 (binary64 display)
```

This is the payload shape required by the next segmented finite-sum import,
but it is not yet a Lean certificate. The center values use 100-decimal
mpmath, and the transcendental evaluation and upward rounding have not yet
been re-proved inside Lean. The curvature payload is also still absent.

The artifact is intentionally separate from record 2529: 2529 freezes direct
per-family rectangle summation because its dependency inflation is too large;
2530 keeps the center sum and error charge separate.

Evidence:

- `scripts/routea_owner_signed_node_center_error_2530.py`
- `results/2530_signed_node_center_error_payload.json`
- `docs/proofs/2528_signed_pointwise_cancellation.md`
- `docs/proofs/2529_signed_point_interval_dependency.md`

Payload integrity repair: the 2530 generator now stores an exact rational
`x_exact` for every node in addition to the decimal display `x`. A dedicated
checker verifies source hashes, all 2561 exact grid coordinates, positive
upward node bounds, exact rational trapezoid reconstruction, and both node sums
below `baseNormUpper2343`. The checker reports margins about 0.09220700 and
0.10388292 for the node sum alone. This fixes a real decimal-display replay
issue at node 1261; it does not certify the transcendental evaluations.
Evidence: `scripts/routea_signed_node_payload_check_2530.py`.
