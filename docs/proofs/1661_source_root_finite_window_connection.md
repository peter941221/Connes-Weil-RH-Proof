# 1661 — source-root finite-window connection

## Formal result

The abstract reverse-limit criterion from 1660 is now instantiated with the
actual source-compressed root.  For

`C = rootConvolution owner`, `J = sourceInclusion lambda`, and
`P_n = kernelIntervalProjection (-(n : Real)) (n : Real) 0`,

the approximant is exactly `J† ∘L P_n ∘L C ∘L J`.  The existing strong-limit
theorem for expanding interval projections, followed by continuity of `J†`,
proves pointwise convergence to `J† ∘L C ∘L J`.

Consequently, a single uniform bound

`sum over any finite basis set of ||J† P_n C J e_i||^2 <= B`

for all `n` implies the full source-compressed survivor-core square-sum.
The focused audit build completed with 3961 jobs, zero errors, zero
`sorryAx`, and only `[propext, Classical.choice, Quot.sound]`.

## Remaining producer

The theorem is a genuine reduction, not the missing estimate itself.  The
remaining analytic task is now the concrete uniform finite-window bound for
the projected root columns, including the limit as the output interval grows.
The finite compact-kernel estimates already cover bounded windows; the open
part is the collective infinite radial tail.
