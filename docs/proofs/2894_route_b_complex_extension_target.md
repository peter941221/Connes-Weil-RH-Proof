# 2894 Route B complex extension target

The real Mathlib object `Real.smoothTransition` cannot be passed directly to
the complex Cauchy interfaces. The required complex extension is the meromorphic
expression

```text
F(w) = (exp(2 * (1/w - 1/(1-w))) - 1)
       / (exp(2 * (1/w - 1/(1-w))) + 1)
```

The formal target is split into two independent obligations:

```text
1. denominator nonzero:
   exp(2 * (1/w - 1/(1-w))) + 1 != 0
   on the closed disk |w - c| <= R, with R = 0.05;

2. differentiability:
   DifferentiableOn ℂ F {w | |w-c| < R}.
```

Only after these are proved can Mathlib's
`DifferentiableOn.hasFPowerSeriesOnBall` produce the Cauchy power series used
by the 2891 arithmetic consumer. The current 2889 interval artifact bounds a
derived polynomial expression; it does not yet prove this denominator condition
for the complex extension.
