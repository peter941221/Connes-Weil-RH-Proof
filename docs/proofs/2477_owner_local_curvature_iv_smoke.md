# 2477 - interval-structure smoke for local curvature

Date: 2026-10-03.

The sampled 2476 local curvature price was ported to interval arithmetic for
one structural check.  Each cell carries interval bounds for bump derivatives
of orders 0, 1, and 2, then the 30-family sum is combined before the weighted
second-derivative charge.  Cells touching a support edge use the global bump
ladder constant for the removed edge sliver, avoiding an invalid interval
division by zero.

This uses `mpmath.iv`, not the project Arb/MPFR certificate engine.  It is
therefore only a structure smoke and cannot be imported into Lean.  Its value
is to test the edge split and containment shape before spending time on an
Arb/MPFR generator.

At 40 cells the natural interval extension reads approximately `1.366e5` for
the summed remainder, versus `1.539e3` in the 2476 sampled price.  The gap is
an interval-dependency failure mode, not evidence against the local method;
the next implementation must split the polynomial/deficit dependence or use
a Taylor enclosure with an explicit remainder.
