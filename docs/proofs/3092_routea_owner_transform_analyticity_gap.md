# 3092 - owner transform analyticity and global nonzero value

Both remaining transform premises are closed for the actual owner:

```text
routeAOrbitTransform_analytic
routeAOrbitTransform_global_nonzero
```

The proof reads the same owner's raw interpolation value at `rho`, which is
exactly 1, proves the selected owner test is nonzero, and then uses the
injectivity of Mathlib's Fourier continuous equivalence to obtain a real
frequency with nonzero transform. The frequency rescaling is carried out
explicitly through `xi = -2 * pi * y`.

The analytic theorem has the required type:

```text
AnalyticOnNhd Real
  (fun xi => routeAOrbitTransform geometry xi) Set.univ
```

The proof reuses `C1XiResidue.differentiable_laplaceAt`, which already proves
complex differentiability of the same bundled Laplace integral at every
complex parameter. That theorem justifies differentiation under the integral
using compact support and an integrable local derivative bound. Mathlib's
complex differentiability-to-analyticity theorem supplies entire analyticity.
Restricting scalars from Complex to Real and composing with `xi -> xi * I`
then gives the actual route transform's real analyticity.

Correction to the earlier gap record: the required Laplace regularity was
already available in the project. No almost-everywhere nonvanishing bridge
is used to replace analyticity. All four declarations in the audit use exactly
`[propext, Classical.choice, Quot.sound]`.
