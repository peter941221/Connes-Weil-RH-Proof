# 3195 Route A Taylor-5 Full-Cell Upper

Status: the two-sided pointwise Taylor-6 remainder bound is verified in Lean.

The theorem `taylor5_upper_on_cell3195` accepts a cell `[left, right]`, a
center strictly inside that cell, global `ContDiff ℝ 6`, and a global bound on
`iteratedDeriv 6`. It handles both branches separately:

```text
position >= center  -> uIcc center position = Icc center position
position <= center  -> uIcc center position = Icc position center
```

In both cases, Mathlib's Lagrange remainder gives the exact sixth-order term
`M6 * (position - center)^6 / 720`. Global smoothness then identifies the
local Taylor coefficients with the fixed cell `Icc left right` coefficients.

This closes the left/right pointwise analytic boundary needed before the
full-cell integral can be connected to the 3193 symmetric polynomial panel.
It does not provide numerical cell data or a producer certificate.

Evidence:

- `build-logs/3195_wsl_build.log`
- `build-logs/3195_wsl_audit.log`

The audit reports exactly `[propext, Classical.choice, Quot.sound]`.
