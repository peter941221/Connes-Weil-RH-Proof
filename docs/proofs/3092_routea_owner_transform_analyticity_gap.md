# 3092 - owner transform analyticity gap

The exact Laplace/Fourier bridge is closed by record 3086. The global nonzero
value is now also closed for the actual owner:

```text
routeAOrbitTransform_global_nonzero
```

The proof reads the same owner's raw interpolation value at `rho`, which is
exactly 1, proves the selected owner test is nonzero, and then uses the
injectivity of Mathlib's Fourier continuous equivalence to obtain a real
frequency with nonzero transform. The frequency rescaling is carried out
explicitly through `xi = -2 * pi * y`.

The remaining named gap is the actual compact-support Fourier/Laplace
analyticity theorem:

```text
AnalyticOnNhd Real
  (fun xi => routeAOrbitTransform geometry xi) Set.univ
```

The current Mathlib snapshot does not provide this theorem for the bundled
compact-support Laplace transform. An almost-everywhere Fourier nonvanishing
bridge cannot substitute for this analytic premise.
