# 2942 Route B independent exponential rectangle re-price

The dependency gap from 2941 was tested by propagating the independently
extracted `a` rectangle through `exp`, quotient, and `H`.  The resulting H
norm upper bound is `13.173294956955326...`, below the conservative Cauchy
budget `M = 13.77903608911727`.

Decision: the local subcell can use the widened independent exponential
rectangle and retain positive budget margin.  This is still a numerical probe;
formal interval soundness remains open.

