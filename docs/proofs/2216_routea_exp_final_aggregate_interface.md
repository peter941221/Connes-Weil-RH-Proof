# 2216 — Final finite AMP aggregation interface

Date: 2026-09-29

Consumer: the healthy `CompactLog` B5 selected detector, preserving the
actual source-zero owner and the downstream same-owner `qw >= 0` obligation.

The new audited theorem
`norm_add_sum_mul_exp_add_sub_exp_le` combines the analytic exponential
perturbation and finite-sum bounds with a final accumulator radius:

```text
‖r + Σᵢ cᵢ (exp(zᵢ + δᵢ) - exp(zᵢ))‖
  ≤ ‖r‖ + Σᵢ 2 ‖cᵢ‖ exp(Re zᵢ) ‖δᵢ‖,
```

under `‖δᵢ‖ ≤ 1` on the finite index set. This is the exact mathematical
shape needed by the GL/Simpson AMP price, including the final summation
rounding radius.

The owning module and paired audit pass in the WSL ext4 mirror. All five
exposed declarations report only `[propext, Classical.choice, Quot.sound]`
and no `sorryAx`.

Artifacts:

- `results/20260929_2216_exp_final_aggregate_module_pass3.log`
- `results/20260929_2216_exp_final_aggregate_audit.log`

Status: `AMP-FINAL-AGGREGATION-INTERFACE-CLOSED /
CONCRETE-IEEE-RADIUS-OPEN`.
Concrete IEEE/ulp radii, actual-owner transfer, and the signed producer
margin remain open. No RH claim follows.
