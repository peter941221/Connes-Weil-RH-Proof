# 2893 Mathlib Cauchy interface survey

The ext4 Mathlib checkout is at revision `c5ea00351c2`. The relevant source is
`Mathlib/Analysis/Complex/CauchyIntegral.lean`.

The available interfaces include:

```text
Differentiable.hasFPowerSeriesOnBall
DifferentiableOn.hasFPowerSeriesOnBall
DiffContOnCl.hasFPowerSeriesOnBall
Complex.hasFPowerSeriesOnBall_of_differentiable_off_countable
```

These produce `HasFPowerSeriesOnBall f (cauchyPowerSeries f c R) c R`.
The project’s current Lean seam consumes the resulting circle supremum as an
explicit real bound and closes the geometric arithmetic tail. The remaining
formal bridge must instantiate one of the interfaces above for the concrete
Route B complex function and connect its coefficient norm bound to the stored
interval certificate.
