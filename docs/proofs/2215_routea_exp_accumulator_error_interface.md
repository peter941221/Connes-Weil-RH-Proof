# 2215 — Finite accumulator error interface

Date: 2026-09-29

Consumer: the healthy `CompactLog` B5 selected detector and its same-owner
`qw >= 0` producer. The premise removed here is the unstructured passage from
per-term bounds to a final complex GL/Simpson readout.

The audited theorem
`norm_add_sum_approx_sub_le` states that for a finite index set, exact terms
`x`, approximated terms `y`, per-term radii `E`, and a final accumulator error
`r`,

```text
‖r + (Σ y - Σ x)‖ ≤ ‖r‖ + Σ ‖E‖,
```

whenever `‖yᵢ - xᵢ‖ ≤ ‖Eᵢ‖` on the index set. This is the precise interface
needed to plug IEEE/ulp bounds into the analytic finite-sum propagation of
2214.

The owning module and paired audit pass in the WSL ext4 mirror. The audit
reports only `[propext, Classical.choice, Quot.sound]` for all four exposed
theorems and no `sorryAx`.

Artifacts:

- `results/20260929_2215_exp_accumulator_module_pass5.log`
- `results/20260929_2215_exp_accumulator_audit.log`

Status: `ACCUMULATOR-ERROR-INTERFACE-CLOSED /
IEEE-ULP-RADIUS-OPEN`.
The theorem does not supply the concrete IEEE radii or complete-owner
transfer, so it is not yet a producer margin or RH proof.
