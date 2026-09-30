# 2283: Filon interpolation residual derivative price

Date: 2026-09-30

Decision: scoped residual-price no-go for the current local polynomial Filon profiles.

## Question

Before implementing a directed derivative enclosure, can the standard Lagrange interpolation residual formula plausibly fit the finite-tail numerical scale?

## Method

For degree n on a panel of width L, the screen uses the Lagrange residual shape `L^(n+1) / (2^(n+1) (n+1)!)` multiplied by a sampled absolute `(n+1)`-st derivative of the corrected owner. It evaluates three interior points per panel with 50-digit mpmath differentiation. This is deliberately a price screen: sampled maxima are not uniform derivative bounds.

## Result

```text
profile       base residual integral       corr residual integral
12:12         7.4658126247e11              1.0787663867e11
18:16         4.0754980539e10              5.8071420425e9
24:20         4.2856544169e8               7.6334075791e7
```

The best tested profile still prices the base residual at about `4.29e8` and the correction residual at about `7.63e7`, while the corresponding transforms in the earlier screens are around `1e-3` to `1e-2`. The generic derivative-envelope route therefore loses many orders of magnitude before kernel coupling or infinite-tail assembly.

## Interpretation

This rejects the current generic Lagrange-derivative residual mechanism as a practical supplier for the Filon tail. It does not prove that a representation-aware residual bound is impossible. Reopening requires a named cancellation-preserving residual identity, not merely more derivative samples or higher polynomial degree.

## Nonclaims

- Sampled derivative maxima are not uniform derivative enclosures.
- The price ignores kernel coupling and is only a feasibility screen.
- No hgap supplier, producer GO, selected-detector readback, or RH conclusion follows.

## Reproduction

```text
python scripts/routea_filon_residual_derivative_price_2283.py --samples 3
python -m unittest discover -s scripts -p 'routea_filon_residual_derivative_selftest_2283.py' -v
```
