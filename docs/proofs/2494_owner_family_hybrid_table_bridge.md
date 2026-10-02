# Record 2494: analytic consumer bridge for the hybrid table

The new Lean bridge exposes the exact remaining obligation for using the 2492
payload: for every production-grid cell, the analytic hybrid curvature must
be at most the corresponding rational table entry. Given that `hcell`, Lean
derives the strip-norm upper bound and charges the table entries through the
local `step^3/12` remainder. The table itself remains data and is not treated
as an enclosure proof.

The audit checks the bridge theorem's axioms. No producer GO or RH claim is
made. Evidence: `ConnesWeilRH/Dev/C1RouteAOwnerFamilyHybridTableBridge2494.lean`
and its audit file.
