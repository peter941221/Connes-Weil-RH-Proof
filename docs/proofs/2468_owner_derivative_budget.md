# 2468 - actual owner derivative-budget attachment

Date: 2026-10-02.

The single-family derivative budget from the existing owner derivative
machinery is now instantiated with the exact 2460 owner arrays
`ownerCoef_2463`, `ownerMod_2463`, and `ownerRad_2463`.  The finite 30-family
sum is differentiated term by term, and
`ownerPanelIteratedDerivBudget_2468` proves the norm bound for every order
`≤ 4`; `ownerPanelSecondDerivBudget_2468` exposes the order-2 instance for
the 2457 ζ interface.

The module and audit build in the fresh ext4 mirror
`/home/peter/verify/cwr-2460` with Lean 4.30.  Both declarations report
exactly `[propext, Classical.choice, Quot.sound]`; no `sorryAx` or project
axiom was reported.

This is the derivative-budget side only.  The numerical budget value,
weighted node sum, trapezoid assembly, and final strip attachment remain
open.  No GO or RH claim.

Evidence: `ConnesWeilRH/Dev/C1RouteAOwnerDerivativeBudget2468.lean` and
`ConnesWeilRH/Dev/C1RouteAOwnerDerivativeBudget2468Audit.lean`.
