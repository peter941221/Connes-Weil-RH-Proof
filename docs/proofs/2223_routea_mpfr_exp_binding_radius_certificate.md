# 2223 — MPFR directed-rounding binding-node certificate

Date: 2026-09-29

Consumer: the healthy `CompactLog` B5 selected detector, actual
`sourceNontrivialZeroSet` owner, same-owner `qw >= 0` producer.

The 2220/2222 atom certificates were lifted to the complete quadrature rule at
the 2211 binding node (node 2): all 30 families, GL points, and 12 Simpson
panels with `NSEG=1100`. The evaluator calls `libmpfr.so.6` directly at 256
bits. `exp`, `sin`, and `cos` are evaluated with both directed roundings, and
the products are converted to binary64 with directed roundings before charging
the distance to NumPy's returned complex value.

```text
GL implementation charge             3.519729311380404e-12
Simpson implementation charge        3.520126088671097e-12
total                                7.039855400051501e-12
ratio to 2211 target                 1.1254706710389811e-07
max component radius                 5.048709793414477e-29
```

The independent MPFR ABI self-test enclosed `exp(1)`, `sin(1)`, and `cos(1)`
between their RNDD/RNDU binary64 conversions. Thus the 2223 result is a
correctly-rounded backend price on this node, not an mpmath cross-check.

This closes the transcendental-library implementation remainder at the
binding node with a large margin. It does not yet certify the binary64 input
construction of `q`, finite-sum accumulation, the other 29 nodes, or complete
owner transfer. Those are separate charges; no RH claim follows.

Artifacts:

- `results/2223_mpfr_exp_binding.json`
- `results/20260929_2223_mpfr_exp_binding.log`
- `results/20260929_2223_mpfr_abi_selftest.log`
- scripts: `scripts/routea_weighted_zero_mpfr_exp_binding_2223.py`,
  `scripts/routea_mpfr_abi_selftest_2223.py`

Status: `MPFR-DIRECTED-EXP-RADIUS-BINDING-NODE`; no RH claim.
