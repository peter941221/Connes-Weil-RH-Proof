# 1856 - Base seminorm quantitative boundary

Date: 2026-09-23.

Status: Formal API audit; no no-go or RH claim.

The active geometric contraction route needs the strict inequality

```text
2 * SchwartzMap.seminorm Complex 0 0 base.test < 1.
```

The current base/correction construction does not provide this quantitative
field. `exists_residualWindow_correction_with_quadratic_decay` returns support,
finite Laplace interpolation, nonnegative quadratic tail constant `C`, and the
vertical quadratic estimate. Its underlying
`fixed_window_finite_mellin_surjective` theorem returns only a compact smooth
test, support, and finite Mellin values. Neither declaration returns a
zero-order Schwartz seminorm bound.

Therefore `C` cannot be substituted for a seminorm bound. The next producer
brick must add a quantitative seminorm witness to the finite-window base
construction, or introduce an explicit test family with a proved seminorm
estimate. This is an interface boundary, not a route no-go result.
