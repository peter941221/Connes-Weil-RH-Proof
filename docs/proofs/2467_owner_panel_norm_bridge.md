# 2467 - owner panel norm bridge

Date: 2026-10-02.

The universal panel rectangle from 2466 now feeds the scalar strip
integrand.  `ownerPanelNormBound_2467` converts the contained 30-family
complex sum into the 2453 rectangle norm bound, and
`ownerPanelWeightedNormBound_2467` lifts it through the nonnegative factor
`exp (σ*x)`.  No node values, trapezoid sum, or numerical premise is
introduced.

The module and audit build in the fresh ext4 mirror
`/home/peter/verify/cwr-2460` with Lean 4.30.  Both declarations report
exactly `[propext, Classical.choice, Quot.sound]`; no `sorryAx` or project
axiom was reported.

The derivative/zeta bound and weighted node-sum certificate remain open.
No GO or RH claim.

Evidence: `ConnesWeilRH/Dev/C1RouteAOwnerPanelNormBridge2467.lean` and
`ConnesWeilRH/Dev/C1RouteAOwnerPanelNormBridge2467Audit.lean`.
