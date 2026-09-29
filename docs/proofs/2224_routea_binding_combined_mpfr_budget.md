# 2224 — Binding-node input plus MPFR combined budget

Date: 2026-09-29

Consumer: the healthy `CompactLog` B5 selected detector, actual
`sourceNontrivialZeroSet` owner, same-owner `qw >= 0` producer.

The 2217 input/operation forward-error price and the 2223 MPFR
implementation-radius price were assembled on the same binding node and the
same full quadrature rule.

```text
2217 input/operation parameterized       2.459424789942387e-08
2223 exp/sin/cos MPFR certified          7.039855400051501e-12
assembled                               2.460128775482392e-08
2211 target                             6.2550323e-05
assembled / target                      3.933039283398092e-04
```

This materially shrinks the remaining binding-node obligation: the
transcendental library implementation is negligible relative to the existing
input/operation price. The 2217 term is still only a parameterized IEEE
forward-error price, not an outward certificate. Other nodes, finite-sum
accumulation, complete owner transfer, and the signed producer margin remain
open.

Artifacts:

- `results/2224_binding_combined_budget.json`
- `results/20260929_2224_binding_combined_budget.log`
- script: `scripts/routea_weighted_zero_binding_combined_budget_2224.py`

Status: `BINDING-NODE-PARAMETERIZED-INPUT-PLUS-MPFR`; no RH claim.
