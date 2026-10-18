# 2869 Route B D4 sign-partition probe

This record completes the three requested steps at the diagnostic/interface
level. The rational zero brackets are `[1353/10000, 677/5000]` and
`[757/2500, 3029/10000]`. The fourth derivative has opposite signs at the
ends of both brackets; its pointwise sign pattern away from the brackets is
`+,-,+`. Using the three outer intervals and endpoint variation
of the third derivative gives:

```text
variation bounds: 110.5668058048, 166.2777890350, 39.7108998007
four-times sum:   1266.2219785624 < 1500
```

The Lean interface is
`ConnesWeilRH/Dev/C1RouteBD4SignPartition2869.lean`. It proves the rational
arithmetic target from explicit variation inputs. The analytic obligations are
still open: prove the sign on each interval, prove the zero brackets, and
connect the variation bounds to the actual `iteratedDeriv` owner.

The WSL Lean invocation was attempted but the environment reported that the
localhost proxy was not mirrored into WSL NAT mode. No analytic theorem is
claimed from that failed build attempt.
