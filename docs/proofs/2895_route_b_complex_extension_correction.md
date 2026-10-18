# 2895 Route B complex extension correction

The 2894 target exposed a structural issue. The Cauchy circle used by the
right-endpoint Taylor argument is centered at `t = 0`, but the raw expression

`exp(2 * (1/t - 1/(1-t)))`

has an essential singularity at `t = 0`. Therefore it cannot be used directly
as a holomorphic function on the Cauchy disk.

The correct owner variable is the removable combination

```text
Q(t) = (1 + tanh(2t/(1-t^2))) / 2
```

with `Q(0) = 1/2`, represented through its even/odd power-series extension.
The formal proof target must first construct this extension (or a centered
power series for `Q`) and prove equality with the real logistic function away
from zero. Only then can `HasFPowerSeriesOnBall` be applied to the centered D4
expression. A denominator-nonzero proof for the raw exponential quotient is
not sufficient and must not be consumed as the Cauchy disk certificate.
