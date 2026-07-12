# CC20 Diagonal Limit Series Target

Date: 2026-07-12

Status: symbolic verification only; not a Lean theorem.

Expanding the explicit non-diagonal `Q(delta)` formula at `rho = 1 + e`
gives:

```text
q_reg(1+e) =
  8*pi^2/9 + Si(4*pi)/(4*pi) - 1/2
  + (4*pi^2 - 1)e + O(e^2).
```

The constant agrees exactly with the diagonal extension value used by
`RegularKernel.lean` (numerically `8.39172410732812`). This rules out a wrong
diagonal constant as the current obstruction.

The remaining proof must replace the symbolic `O(e^2)` statement with a Lean
finite-order Taylor or integral-remainder argument for `sin`, `cos`, and the
continuous `Si(x)/x` extension. No source owner or RH route currently consumes
this symbolic calculation.

The first Taylor layer is now formalized: `SineIntegral.lean` proves the
positive and negative slope bounds for `sinc` and
`hasDerivAt_sinc_zero : HasDerivAt Real.sinc 0 0`, using Mathlib's cubic sine
bound and squeeze theorem.
