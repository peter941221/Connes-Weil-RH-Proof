# 089 — Zero-target obstruction to the geometric base contraction

Date: 2026-09-23.

Status: FORMAL scoped no-go for the current geometric-contraction owner.
This is not a no-go for the healthy B5 route and is not an RH result.

The proposed producer required a base `f` with

```text
support f ⊆ (-1, 1)
laplaceAt f 0 = 1
2 * seminorm(f) < 1
```

The same-owner theorem
`seminorm_zero_zero_ge_half_of_laplaceAt_zero_eq_one_of_support_Ioo`
proves the first two conditions imply `1/2 <= seminorm(f)`.  The paired
theorem `not_strict_base_contraction_of_unit_zero_target_of_support_Ioo`
therefore refutes `2 * seminorm(f) < 1` exactly, not numerically.

Evidence: `C1P2BaseSeminormBound.lean` and its paired Audit; build log
`build-logs/20260923_base-nogo7.log` completed successfully with 3664 jobs,
zero `error:` lines, and standard-axiom audit output.  Classification:
formal project no-go.

Consequence: demote the geometric-contraction exits in [088] from active
producer targets.  The live producer returns to the detector-specific signed
physical-kernel budget and the C3' phase-locked certificate in [080].
