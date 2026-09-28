# 2063/2064 - High-order tail branch audit

Date: 2026-09-28.

The high-order tail branch splits into two different statements.

2063 measured a strong candidate. Using the actual one-copy G8-H owner, the
m=6400 coefficient path, derivative orders through `r = 48`, and a 100x stress
factor on the measured total variations, the candidate envelope on
`160 <= |xi| <= 1e6` was `8.096106404656881e-283`. This is far below both
`|Q1600| = 3.406049871881275e12` and the L2 charge
`4.412215566637855e10`.

That is not yet a proof because the `N_r` values were measured with mpmath.

2064 then tested the obvious proof port: expand the derivative polynomial and
integrate the termwise absolute monomial majorant. It fails badly:

```text
+-------+----------------------+----------------------+----------------+
| order | termwise bound       | measured N_r        | bound / N_r    |
+-------+----------------------+----------------------+----------------+
| 12    | 8.506e8              | 8.358e0             | 1.018e8        |
| 24    | 2.625e35             | 1.986e20            | 1.322e15       |
| 36    | 4.541e65             | 1.121e45            | 4.050e20       |
| 48    | 2.906e99             | 2.293e73            | 1.267e26       |
+-------+----------------------+----------------------+----------------+
```

Decision: `TERMWISE_ABSOLUTE_MAJORANT_DEAD`.

This is a scoped no-go for the termwise absolute expansion, not for the
high-order tail mechanism itself. The measured N_r is small because of
substantial sign/zero cancellation in the derivative polynomial. The next
admissible move is a validated sign-partition or root-isolation computation of
`int |phi^(r)|`, with an explicit enclosure; reusing the termwise absolute
majorant is prohibited.

Artifacts:

- `results/2063_route_a_high_order_tail_price.json`
- `results/2064_diag_high_order_bound.json`
- `scripts/routea_high_order_tail_price_2063.py`
- `scripts/diag_high_order_bound_2064.py`
