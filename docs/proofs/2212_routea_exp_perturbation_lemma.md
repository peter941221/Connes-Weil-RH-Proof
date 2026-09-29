# 2212 — Formal exponential perturbation lemma

Date: 2026-09-29

Consumer: the healthy `CompactLog` B5 selected-detector producer, whose final
consumer is the same-owner `qw >= 0` obligation and then `SourceRH`.
Owner: the actual selected `sourceNontrivialZeroSet` owner; this brick itself
is owner-independent and is intended to consume an owner-specific bound on
the complex exponent perturbation `‖δ‖`.

The new theorem
`ConnesWeilRH.Source.C1RouteAExpPerturbation.norm_exp_add_sub_exp_le` proves
the AMP propagation inequality

```text
‖exp (z + δ) - exp z‖ ≤ 2 * exp (Re z) * ‖δ‖,
```

under `‖δ‖ ≤ 1`. It is derived from `Complex.exp_add`, the exact complex norm
identity, `Complex.norm_exp`, and Mathlib's unit-ball exponential remainder
bound. The module and paired audit both pass in the WSL ext4 mirror. The audit
reports exactly `[propext, Classical.choice, Quot.sound]` and no `sorryAx`.

Artifacts:

- `results/20260929_2212_exp_perturbation_module_pass4.log`
- `results/20260929_2212_exp_perturbation_olean_pass1.log`
- `results/20260929_2212_exp_perturbation_audit_pass2.log`

Status: `EXP-PERTURBATION-LEMMA-CLOSED / OWNER-AMP-ASSEMBLY-OPEN`.
This removes the formal exponential propagation premise from the AMP pricing
step, but does not yet prove the full outward floating-point interval model,
complete-owner transfer, or the selected-detector signed producer margin.
No RH claim follows.
