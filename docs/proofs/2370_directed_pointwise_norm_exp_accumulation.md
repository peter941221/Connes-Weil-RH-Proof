# 2370 - Directed pointwise norm/exp accumulation

日期：2026-10-02。

The full-grid accumulator has been upgraded beyond the 2369 binary64-term
audit. For each 2242 point-box rectangle, the worker now computes
`sqrt(max|Re|^2 + max|Im|^2)` in 256-bit MPFR with `RNDU`, computes the
exponential weight from the binary64 coordinate with directed `RNDU`, applies
the endpoint half-weight with `RNDU`, and accumulates the result with a
per-span reset and ordered parent `RNDU` reduction. The resulting displayed
values remain:

```text
2.6867143296475287
8606.214397650678
90.78788225375544
125446.71132157759
```

This closes the pointwise norm/weight and accumulation layer conditional on
the directed 2242 rectangle bounds. It does not yet prove the point-box
function identity for the producer owner and does not include the
composite-trapezoid remainder. Producer GO remains false.

Status: `DIRECTED_POINTWISE_NORM_EXP_ACCUMULATION_ONLY`.
