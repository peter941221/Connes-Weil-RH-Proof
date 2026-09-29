# 2207 — Vector-split forward-rounding allowance

Date: 2026-09-29

Record 2206 supplied the full 30-node vector-aware endpoint-split price at
`NSEG=1000`. Record 2207 prices floating accumulation and coefficient
multiplication on its correction binding row (node 2), keeping the computed
GL-minus-S value cancellation and charging only absolute term sums for
rounding.

## Reading

```text
GL allowance                         7.8069841e-6
Simpson allowance                    4.8818835e-6
coefficient rounding                 6.7767136e-12
total allowance                      1.2688874e-5
allowance / 2206 vector bound        0.17562276
```

The correction total price is therefore approximately
`8.494e-5` at this screen. With the 2201 inverse-norm control this is about
`1.01e-4` relative correction movement, close to but still within the
pre-priced `1e-4` scale in record 2199; the direct-product signed-margin
headroom is much larger.

## Status

Status: `VECTOR-SPLIT-ROUNDING-PRICED / REFINEMENT-RECOMMENDED`.

The allowance is still computed from stored floating term sums and does not
include an analytic transcendental enclosure. The full-owner vector split
therefore remains unpriced as a formal certificate. Raising `NSEG` modestly
(about 1100) is the next tightening step before the matrix-action enclosure
is assembled. No producer theorem or RH claim follows.

