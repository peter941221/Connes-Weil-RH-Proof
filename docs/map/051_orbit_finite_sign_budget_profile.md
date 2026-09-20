# 051 - Orbit finite sign budget profile

Date: 2026-09-20.

Authority: supporting formal interface under the binding B5 route in 003 and
004. Route selection is unchanged.

Record 1743 turns the open `orbitWindowSemiLocalGate` for one raw orbit owner
into an exact finite-range bilateral-profile inequality. Together with 050,
the arithmetic side is now an explicit finite sum indexed by the detector's
own support/orbit radius.

This closes the representation/reduction layer only. The aggregate
archimedean-plus-prime sign remains open and is the next mathematical target.
Evidence: `C1OrbitFiniteSignBudget.lean` and its audit,
`build-logs/shortest_route_20260920_sign_budget_v3.log`, standard axioms only.
