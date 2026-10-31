# 3237: Route-A integrand alignment boundary

Status: blocking no-go for reusing the 3204 negative array.

The formal aggregate target in records 3208-3230 is

```text
weightedExternal3201 sigma coefficients modulations x
= Re(exp(sigma * x) * externalPhysical2344 coefficients modulations x)
```

The external 3204 evaluator calls `jets(family, x, sigma, order)`. Its
zero-th returned entry is built from `raw[j + 2]`, so it is the second
derivative of the weighted family. Its Taylor-6 cell formula therefore bounds
the integral of the weighted second derivative, not the integral of
`weightedExternal3201` itself.

The distinction is structural:

```text
3204 `jets(...)[0]`
        |
        +--> weighted second derivative
        |    negative diagnostic aggregate near -3.51e-9
        |
formal 3225/3230 `hvalue`
        |
        +--> weighted original function value
             required for the current interval-integral theorem
```

The 3236 Lean taxi-ball theorem proves membership for the unweighted
`externalPhysical2344` family sum at cell 17168. It does not prove the
weighted original value, a negative sign, or any derivative identity.

Independent reproduction at the 17168 midpoint gives, approximately:

```text
unweighted externalPhysical real value       +52.2935
weighted sigma = -1/2 real value              +88.8289
3204 weighted second-derivative diagnostic    negative; old cell upper -38.0161
```

These numbers are diagnostics, not Lean certificates. They are sufficient to
reject the old interpretation of `3204.value_upper` as a bound on the current
formal `hvalue` object.

The next valid routes are:

1. Extend the correlated evaluator to the weighted original function, then
   prove all remaining midpoint and derivative bounds for that exact object.

2. If the intended mathematics is the second-derivative channel, introduce
   an explicit theorem identifying its integral with the producer's required
   detector quantity, including boundary terms and the same owner/readback.
   No such transfer is currently closed.

Until one route is closed, the 3204 negative array must remain external
diagnostic data and cannot feed `producer_go`.
