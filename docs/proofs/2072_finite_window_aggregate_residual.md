# 2072 - Aggregate finite-window residual screen

Date: 2026-09-28.

Status: NAIVE-FIRST-DERIVATIVE-BOUND-DEAD.

The sigma and all visible-prime channels were first recombined into one
aggregate kernel before multiplying by the common same-owner weight. This keeps
the observed cancellation intact. The aggregate trapezoid readings are:

```text
step       aggregate value
0.020   -3.406049851783479e12
0.010   -3.406049851783849e12
0.005   -3.406049851781223e12
```

The refinement is consistent with the 2071 signed decomposition. However, the
finite-difference L1 derivative diagnostic is about `2.84e16` to `3.08e16`.
A standard first-derivative composite-trapezoid remainder would therefore be
on the order of `step * variation`, around `1e14` at the coarsest grid. That is
larger than the negative margin by roughly two orders of magnitude.

Decision: `NAIVE-FIRST-DERIVATIVE-BOUND-DEAD`. This is a scoped no-go for the
single global first-derivative variation estimate, not for finite-window signed
quadrature. The next admissible mechanism must exploit higher-order smoothness,
panel cancellation, or an Euler–Maclaurin remainder for the aggregate object.
Independent channelwise absolute bounds remain invalid because their measured
sum is already about `1.23e15`.

Artifact: `results/2072_finite_window_aggregate_residual.json`.
Script: `scripts/routea_finite_window_aggregate_residual_2072.py`.