# 1776 — Complete Schwartz-L2 kernel readback

Date: 2026-09-21

## Claim

For any `MemLp` input admitting a Schwartz sequence converging in L2, the
Plancherel root convolution has the honest translated-kernel integral formula
almost everywhere.

## Formal status

`sourceKernelReadback_ae_of_schwartz_l2_tendsto` composes records 1774 and
1775.  The approximant readback is supplied by the Schwartz-core theorem, and
the pointwise row limit is supplied by the exact L2-to-Holder bridge.

The resulting interface leaves the active S3 path with the annular
kernel-diagonal majorant as the next analytic consumer.  No positivity or RH
conclusion is asserted.
