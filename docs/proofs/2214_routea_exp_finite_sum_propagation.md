# 2214 — Finite-sum exponential propagation

Date: 2026-09-29

Consumer: the healthy `CompactLog` B5 selected detector, with the same-owner
`qw >= 0` obligation as the downstream producer. This brick removes the
remaining analytic aggregation premise after 2213: the coefficient-weighted
exponential perturbation bound must hold after summing all finite quadrature
terms.

For a finite index set `s`, coefficient family `c`, exponent family `z`, and
perturbations `δ`, the audited theorem proves

```text
‖Σᵢ cᵢ (exp(zᵢ + δᵢ) - exp(zᵢ))‖
  ≤ Σᵢ 2 ‖cᵢ‖ exp(Re zᵢ) ‖δᵢ‖,
```

provided `‖δᵢ‖ ≤ 1` on `s`. The owning module and paired audit pass in the
WSL ext4 mirror. All three declarations in the module use only
`[propext, Classical.choice, Quot.sound]`; no `sorryAx` occurs.

Artifacts:

- `results/20260929_2214_exp_sum_module_pass3.log`
- `results/20260929_2214_exp_sum_audit.log`

Status: `EXP-FINITE-SUM-PROPAGATION-CLOSED /
IEEE-SUMMATION-CERTIFICATE-OPEN`.
This does not yet certify the stored floating-point operands, operation
rounding, or transfer from the 30-node candidate screen to the complete
source-zero owner. No RH claim follows.
