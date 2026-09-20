# 1747 - Orbit geometry restores health on the same owner

Date: 2026-09-20.

Status: FORMAL owner-alignment reduction; the signed budget remains open.

The raw `OrbitG8Geometry` package already contains the target values, square
zero control, fourth-order tail, dyadic height bound, and support data needed
by the existing strict healthy-detector theorem. The new theorem
`healthyDetectorData_of_orbitG8Geometry` reconstructs
`HealthyYoshidaDetectorData rho g` for that exact geometry owner.

This removes the last existential-witness mismatch. Combined with record
1746, the shortest producer contract is now only:

`for every right-hand off-line zero, there exist g and OrbitG8Geometry rho g
whose actual finite-range signed budget holds.`

No semi-local sign is proved here and no RH claim is made. The paired G8R0 and
P2 audits passed in `build-logs/shortest_route_20260920_orbit_budget_only_v1.log`:
3784 jobs, zero `error:` lines, zero `sorryAx`, and standard axioms only.
