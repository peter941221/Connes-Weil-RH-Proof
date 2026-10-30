# 3194 Route A Taylor-6 Remainder

Status: one-sided pointwise remainder bound verified in Lean.

The theorem `taylor5_upper_on_right_half3194` uses Mathlib's Lagrange-form
Taylor theorem `taylor_mean_remainder_lagrange_iteratedDeriv`, rather than
`taylor_mean_remainder_bound`. The latter has denominator `5! = 120`; it is
therefore too weak for the sixth-order coefficient required by the cell panel.
The Lagrange theorem gives the exact `6! = 720` denominator. On a cell
half-interval `[center, right]`, a sixth-derivative bound `M6` gives

```text
f(x) <= Taylor5(f, center, x) + M6 * (x-center)^6 / 720
```

The theorem requires global `ContDiff ℝ 6` and a global bound on
`iteratedDeriv 6`. This is intentional: with only `ContDiffOn` on a closed
interval, Mathlib's `uIcc` Taylor theorem does not justify identifying the
endpoint `within` derivatives of two different intervals. The global
smoothness assumption makes that identification explicit and connects
directly to the existing `correctedPhysical_sixth_iteratedDeriv_budget2350`
theorem.

Evidence:

- `build-logs/3194_wsl_build.log`
- `build-logs/3194_wsl_audit.log`

The audit reports exactly `[propext, Classical.choice, Quot.sound]`.
