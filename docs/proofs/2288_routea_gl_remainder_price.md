# 2288: classical Gauss-Legendre remainder price

Date: 2026-09-30

Decision: the classical derivative-remainder mechanism is priced out for the current oscillatory owner.

## Method

For an order-n Gauss-Legendre rule on each panel, the classical remainder contains a derivative of order `2n`. This screen samples that derivative at two interior points per panel using 45-digit mpmath differentiation and multiplies it by the standard Gauss-Legendre remainder coefficient. The sampled maxima are not uniform bounds; the purpose is feasibility pricing only.

The first run uses `xi = 40` and the same corrected owner as records 2286–2287.

## Result

```text
configuration     base remainder price       corr remainder price
8 panels/order 8       4.9847e21                 5.0292e22
8 panels/order 16      5.8766e33                 8.5147e33
16 panels/order 8      1.6510e17                 8.1633e17
16 panels/order 16     2.9059e24                 1.7336e24
```

Even the least expensive sampled row is at least `1.65e17` for base and `8.16e17` for corr, before kernel weighting and before the infinite xi tail. The order-16 rows are worse because the high derivative order dominates the nominal GL coefficient.

## Decision

Freeze the classical derivative-form GL remainder for this owner. It is not a viable hgap supplier. This does not reject Filon, contour deformation, or another representation-aware oscillatory rule whose remainder does not pay the raw `2n`-th derivative of the full high-frequency integrand.

## Nonclaims

- Sampled derivative maxima are not uniform derivative enclosures.
- The finite xi sample is not the infinite tail.
- No hgap supplier, producer GO, selected-detector readback, or RH conclusion follows.

## Reproduction

```text
python scripts/routea_gl_remainder_price_2288.py --samples 2 --xis 40 --profiles 8:8,8:16,16:8,16:16
python -m unittest discover -s scripts -p 'routea_gl_remainder_selftest_2288.py' -v
```
