# 2213 — Coefficient-weighted exponential propagation

Date: 2026-09-29

Consumer: the selected healthy `CompactLog` B5 detector and its same-owner
`qw >= 0` producer obligation. The immediate premise removed is the missing
formal propagation of the AMP exponent perturbation through each interpolation
coefficient.

The paired Lean module now proves, for `‖δ‖ ≤ 1`,

```text
‖c * (exp (z + δ) - exp z)‖
  ≤ 2 * ‖c‖ * exp (Re z) * ‖δ‖.
```

This is the exact coefficient-weighted shape used by the direct-product
allowance price. The owning module and audit pass in the WSL ext4 mirror;
both declarations have only `[propext, Classical.choice, Quot.sound]` and no
`sorryAx`.

Artifacts:

- `results/20260929_2213_exp_product_module.log`
- `results/20260929_2213_exp_product_audit.log`

Status: `EXP-COEFFICIENT-PROPAGATION-CLOSED /
OUTWARD-FLOAT-INPUT-ASSEMBLY-OPEN`.
The result does not certify NumPy/IEEE values, summation order, or complete
owner transfer, and gives no RH claim by itself.
