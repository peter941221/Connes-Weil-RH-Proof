# 2361 - Segment derivative coordinate charge

日期：2026-10-01。

The coordinate-charge interface from 2360 now includes
`norm_value_le_of_deriv_bound2359`. Given a `HasDerivWithinAt` chain on an
ordered segment and a uniform derivative-norm bound on its half-open cells,
the theorem bounds the value norm at every point by the initial value plus
`C * (x - a)`. This is the analytic shape needed to price a stored-coordinate
node against its affine-grid counterpart.

The theorem is generic over a real normed space and imports no coefficient,
grid, or floating-point value. The remaining application work is substantive:
prove the derivative bound for the weighted corrected physical function,
partition the actual/ideal coordinate pairs by orientation, and charge the
directed numerical accumulation separately.

Status: `ANALYTIC_BRIDGE_ONLY`; producer GO: `false`.
