# 2476 - sampled actual-owner local curvature price

Date: 2026-10-03.

The actual 2460 owner was evaluated with the order-0/1/2 bump derivative
ladder on each cell, combining all 30 families before the final scalar
charge.  This prices the premise introduced by 2475 rather than reusing the
global 2350 maximum.  The probe is sampled binary64 arithmetic only; it is not
a uniform interval enclosure and cannot be imported as a Lean bound.

The artifact is retained to choose the next enclosure design.  Its required
replacement is a directed cellwise bound for the same ladder, with the
family sum and weighted second derivative conventions unchanged.

With 201 samples per cell, the summed remainder price falls approximately
from `7.59e3` at 20 cells to `1.54e3` at 40, `3.39e2` at 80, and `7.88e1`
at 160 cells.  This is a useful feasibility signal for the 2475 interface,
not a proof of those maxima.
