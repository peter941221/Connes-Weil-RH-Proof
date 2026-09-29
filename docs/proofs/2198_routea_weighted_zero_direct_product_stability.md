# Route A record 2198: direct-product stability screen

The live consumer and candidate owner are unchanged from record 2197. This
screen checks whether the direct-product mass improvement survives committed
quadrature refinement.

For `m = 1600, 3200, 6400`, the matrix condition number stayed at
`2.6537319996e5`, and the direct-product `C_upper` at `sigma = 1` was:

```text
m=1600: 77444.14398505211   relative to m=6400: -1.66e-11
m=3200: 77444.14398590974   relative to m=6400: -5.49e-12
m=6400: 77444.14398633520
```

The base and correction solve residuals stayed below `1.81e-11`. Thus the
2197 improvement is not a quadrature-resolution accident in this screen.

The control also exposes the next risk: the largest correction coefficient is
approximately `5.6875e17`. An eventual interval certificate must charge its
forward solve/enclosure error explicitly; coefficient stability alone is not a
proof.

This is still a measured candidate-owner screen, not a complete-owner or RH
certificate. The heavy probe completed with exit 0:
`results/20260929_weighted_zero_direct_product_stability_2198.log`.
