# 1743 - Orbit finite sign budget in bilateral-profile form

Date: 2026-09-20.

Status: FORMAL, supporting brick for the healthy-`CompactLog` B5 mainline.
This is an exact reduction, not a positivity proof and not an RH claim.

For the same selected `OrbitG8Geometry` owner, theorem
`orbitWindowSemiLocalGate_iff_finiteRangeBilateralProfile` rewrites the open
gate as

    archimedeanTerm(square)
      + sum over range(ceil(exp(2*(orbitIndex+2))) + 1)
          vonMangoldt(n) / sqrt(n) * Re(bilateralProfile(square, log n))
      <= 0.

The range is the support-derived finite owner from record 1742. The equality
uses the exact Hermitian bilateral-profile formula for each finite-prime term;
no pointwise sign, cancellation, or external hypothesis is inserted.

This is the shortest remaining executable sign surface: the next analytic
brick must bound this finite weighted profile sum together with the
archimedean term for the selected detector, on the same owner.

Verification: owning module and paired audit built successfully in
`build-logs/shortest_route_20260920_sign_budget_v3.log`, 3664 jobs, zero
`error:`/`sorryAx`, standard axioms only.
