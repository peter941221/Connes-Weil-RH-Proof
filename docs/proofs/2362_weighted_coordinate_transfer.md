# 2362 - Weighted physical coordinate transfer

日期：2026-10-01。

The coordinate bridge now reaches the existing weighted physical-function
owner. `weightedFunction2348_norm_le_of_coordinate_segment2359` derives a
one-sided coordinate transfer from the weighted first derivative on an
ordered segment. Under bounds `|x| ≤ radius`, `‖function x‖ ≤ zeroBound`, and
`‖deriv function x‖ ≤ firstBound`, its charge is
`exp(|sigma| radius) (|sigma| zeroBound + firstBound)` times the coordinate
displacement.

This is an analytic theorem only. It does not yet provide the owner-specific
zero/first bounds for `correctedPhysical`, does not resolve the mixed
orientation of all stored-vs-affine nodes, and does not certify the numerical
accumulation or trapezoid remainder.

Status: `WEIGHTED_ANALYTIC_BRIDGE_ONLY`; producer GO: `false`.
