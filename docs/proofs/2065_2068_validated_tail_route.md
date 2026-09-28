# 2065-2068 - Validated high-order tail route

Date: 2026-09-28.

Status: HIGH-ORDER-TAIL-GO-CANDIDATE. The tail is not yet the complete Route A
producer proof, but this branch now has a concrete validation path.

The measured high-order candidate in record 2063 was very small. The direct
termwise absolute proof port was killed by record 2064. The replacement keeps
the sign/zero structure of the derivative polynomial:

```text
phi^(r)(u) = exp(-K/(1-u^2)) * B_r(u)
B_r(u) = P_r(u) / (1-u^2)^(2r)
```

For `r = 48`, exact rational polynomial construction and SymPy root isolation
find 64 real roots of `P_48` in `(-1, 1)`, with maximum root interval width
below `1e-60`. Partitioning `phi^(47)` at those roots reproduces the measured
`N_48` to relative `8.51e-7` (record 2067).

An interval evaluation of `phi^(47)` on the exact root intervals gives the
following conservative variation upper skeleton:

```text
N48 interval upper proxy = 1.2466403887652727e81
measured N48              = 2.29343747171e73
upper / measured          = 5.4356851e7
```

Even if this factor is charged uniformly to every high-order rung, the 2063
candidate tail scales by the fourth power because the C3' envelope contains
`lb^2 * cc^2`:

```text
2063 candidate tail       = 8.096106404656881e-283
stress-scaled tail        = 7.067948292096522e-260
stress-scaled / L2 charge = 1.6019045727365396e-270
```

This is a strong Go candidate for the `|xi| > 160` tail. Remaining work before
calling it a proved tail is mechanical but mandatory:

1. run the exact-root/interval variation enclosure for every rung used by the
   envelope, not only `r = 48`;
2. certify the root list has no missing multiplicity or endpoint contribution;
3. replace the numerical `1e6` cutoff with an analytic algebraic remainder;
4. carry the resulting tail bound into the same-owner full-line C3' budget.

The termwise absolute-majorant route remains permanently dead. The admissible
route is sign-partition plus validated total variation.

Artifacts:

- `results/2063_route_a_high_order_tail_price.json`
- `results/2064_diag_high_order_bound.json`
- `results/2066_exact_root_isolation.json`
- `results/2067_root_partition_variation.json`
- `results/2068_interval_variation_bound.json`
- `scripts/diag_exact_root_isolation_2066.py`
- `scripts/diag_root_partition_variation_2067.py`
- `scripts/diag_interval_variation_2068.py`
