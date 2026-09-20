# 1749 - Two-point physical profile interpolation

Date: 2026-09-20.

Status: FORMAL local interpolation brick; no sign claim.

Using two compact-log bumps with non-overlapping sample intervals, the new
theorem `exists_twoPointPhysicalInterpolation` constructs a genuine
`CompactLogTest` taking arbitrary prescribed complex values at two selected
physical log points. The scalar and additive operations remain on the same
compact-log owner.

This is a finite physical-profile primitive for the signed budget route. It
does not preserve triple Mellin vanishing, does not construct an orbit
detector, and does not imply `qw >= 0` or RH. The next task is constrained
interpolation: retain the three Mellin zero conditions and the off-line
detector target while controlling finite prime-log samples.

Evidence: `C1P2TwoPointPhysicalInterpolation.lean` and its Audit;
`build-logs/shortest_route_20260920_two_point_physical_v1.log` reports 3480
successful jobs, zero `error:` lines, zero `sorryAx`, and standard axioms only.
