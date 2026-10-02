# 2440 — Route A bump-factor bounds

Date: 2026-10-02.

For positive radius, Lean now proves the analytic bounds
`0 ≤ widthBump radius position ≤ 1`, including the outside-support branch and
the strict interior denominator argument.  These are exact owner lemmas for
the bump factor; no floating-point or MPFR endpoint is involved.

The phase factor and the directed numerical enclosure of the bump value remain
separate obligations.
