# 2912 Route B coarse-trigonometric bound no-go

For the first local angular subcell, propagating the deliberately coarse
rectangle

```text
t.re in [0.02, 0.03]
t.im in [-0.045, -0.04]
```

through the same interval evaluator gives a final `H` norm upper bound of
approximately `21.9087558335`, exceeding the Cauchy budget
`M = 13.77903608911727`.  Using only `cos in [0,1]` and `sin in [-1,0]`
includes the origin and makes the quotient interval unbounded.

Decision: basic monotonicity bounds are insufficient.  The endpoint proof must
use a tighter Taylor/Lipschitz enclosure before the analytic interval chain can
meet the Cauchy margin.  This is a scoped method no-go, not a Route-B or RH
no-go.

