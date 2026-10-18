# 2868 Route B D4 first-principles analysis

The refinement probe shows that the obstruction is the enclosure method, not
the underlying D4 magnitude. For the owner function

`T(u) = exp(-(1/u - 1/(1-u))) / (1 + exp(-(1/u - 1/(1-u))))`,

an independent high-precision pointwise differentiation and split quadrature
gives

```text
integral from 1/4096 to 1/2 of |T''''(u)|  = 316.5553967499
four times this integral                       = 1266.2297607019
```

The last number is below the registered D4 target 1500. The fourth derivative
changes sign at approximately `u = 0.1353562534` and `u = 0.3028109990`.
The current cell charge instead integrates a per-cell supremum of an interval
jet and converges near 4000, paying the same local peak repeatedly. This is a
classic sup-before-integral loss.

The mathematically promising route is therefore a sign-partitioned D4
enclosure: certify the two zero brackets, prove a one-sided sign on the three
subintervals, and integrate a direct enclosure for `T''''` rather than summing
cell suprema. This is only a numerical diagnosis; the pointwise calculation
is not a Lean certificate.
