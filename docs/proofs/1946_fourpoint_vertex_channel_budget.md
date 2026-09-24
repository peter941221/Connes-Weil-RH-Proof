# 1946 — Vertex gate channel budget

Date: 2026-09-24

## Result

Using the certified 1918 gate entries, evaluate the actual four-point
quadratic at its owner-specific vertex `lambda = B'/(2*C)`. On all 18
committed-class cases:

- the full gate value is strictly negative;
- the Archimedean contribution to that same linear gate value is strictly
  negative;
- the finite-prime contribution is strictly negative.

The smallest observed full relative margin is approximately `4.96e-5`.
The least negative full value is approximately `-9.87e5`.

## Route impact

This refines the next analytic target. At the owner-specific vertex, the
linear gate functional splits as

```text
Q_full(lambda) = Q_arch(lambda) + Q_prime(lambda).
```

The committed-class probe suggests proving the two signed inequalities
`Q_arch(lambda_vertex) < 0` and `Q_prime(lambda_vertex) < 0` separately,
while retaining the actual owner and its visible-prime set. This is a more
structured target than estimating the determinant by expanding arch, prime,
and cross determinant blocks. It does not remove the need to prove that the
selected owner admits the required parameter bounds, nor does it prove the
gate sign.

## Reproducibility

Probe: `scripts/fourpoint_vertex_channel_budget_1946.py`.

Input: `results/1918_fourpoint_diagonal_sign_certified.json`.

Artifact: `results/1946_fourpoint_vertex_channel_budget.json`.

The probe completed with the resource runner, exit code 0. This is numeric
decision evidence only; no Lean theorem and no RH claim is added.
